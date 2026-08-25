import { readFileSync, writeFileSync, mkdirSync, renameSync } from "node:fs";
import { dirname } from "node:path";

import { canonicalJson, freezeDeep, hashCanonicalTuple } from "../storage/canonical.js";
import { createProjectRelation, relationKey } from "./linked_project.js";
import { canonicalExistingIdentity, canonicalRoot, normalizeRelativePath } from "./paths.js";
import { createWorktreeRecord } from "./worktree.js";

function clone(value) {
  return JSON.parse(canonicalJson(value));
}

function idFor(prefix, label, values) {
  return `${prefix}-${hashCanonicalTuple(label, values)}`;
}

function projectRecord(input, workspaceUid) {
  if (!input || typeof input !== "object") throw new TypeError("project must be an object");
  const key = String(input.key ?? input.projectKey ?? input.name ?? "").normalize("NFC");
  if (!key || !/^[A-Za-z0-9][A-Za-z0-9._~-]*$/.test(key)) throw new TypeError("project key is invalid");
  const projectRoot = input.root ?? input.projectRoot;
  if (typeof projectRoot !== "string" || projectRoot.length === 0) throw new TypeError("project root is required");
  const root = canonicalRoot(projectRoot);
  const uid = input.projectUid ?? input.project_uid ?? idFor("P", "project_v1", [workspaceUid, key]);
  if (typeof uid !== "string" || !/^P-[A-Za-z0-9._~-]+$/.test(uid)) throw new TypeError("project UID must use the P- opaque-id form");
  const revision = input.revisionId ?? input.revision_id ?? input.revision ?? null;
  const record = {
    project_uid: uid,
    key,
    root,
    revision_id: revision === null ? null : String(revision),
    trust: input.trust ?? "reviewed",
    visibility: input.visibility ?? "project",
    metadata: input.metadata === undefined ? {} : clone(input.metadata)
  };
  return freezeDeep(clone(record));
}

/**
 * Registry for one workspace.  It stores identity and relationship metadata;
 * it never infers semantic dependency from a path, symlink, gitlink, or
 * worktree mount.
 */
export class WorkspaceRegistry {
  constructor({ workspaceUid = null, root, schemaVersion = 1 } = {}) {
    if (typeof root !== "string" || root.length === 0) throw new TypeError("workspace root is required");
    this.workspace_uid = workspaceUid ?? idFor("W", "workspace_v1", [canonicalRoot(String(root ?? ""))]);
    if (!/^W-[A-Za-z0-9._~-]+$/.test(this.workspace_uid)) throw new TypeError("workspace UID must use the W- opaque-id form");
    this.root = canonicalRoot(String(root ?? ""));
    this.schema_version = schemaVersion;
    this._projects = new Map();
    this._relations = new Map();
    this._worktrees = new Map();
  }

  registerProject(input) {
    const record = projectRecord(input, this.workspace_uid);
    const prior = this._projects.get(record.project_uid);
    if (prior) {
      if (canonicalJson(prior) !== canonicalJson(record)) throw new Error(`project UID already names different metadata: ${record.project_uid}`);
      return clone(prior);
    }
    for (const existing of this._projects.values()) {
      if (existing.key === record.key) throw new Error(`project key already registered: ${record.key}`);
    }
    this._projects.set(record.project_uid, record);
    return clone(record);
  }

  registerRelation(input) {
    const relation = createProjectRelation(input);
    if (!this._projects.has(relation.from_project_uid) || !this._projects.has(relation.to_project_uid)) {
      throw new Error("both relation endpoints must be registered projects");
    }
    const key = relationKey(relation);
    for (const existing of this._relations.values()) {
      if (relationKey(existing) === key) return clone(existing);
    }
    if (this._relations.has(relation.relation_uid) && relationKey(this._relations.get(relation.relation_uid)) !== key) {
      throw new Error(`relation UID already names a different relation: ${relation.relation_uid}`);
    }
    this._relations.set(relation.relation_uid, relation);
    return clone(relation);
  }

  registerLinkedProject(input) {
    return this.registerRelation(input);
  }

  registerWorktree(input) {
    const record = createWorktreeRecord(input);
    if (!this._projects.has(record.project_uid)) throw new Error(`worktree project is not registered: ${record.project_uid}`);
    const prior = this._worktrees.get(record.worktree_uid);
    if (prior) {
      if (canonicalJson(prior) !== canonicalJson(record)) throw new Error(`worktree UID already names different metadata: ${record.worktree_uid}`);
      return clone(prior);
    }
    this._worktrees.set(record.worktree_uid, record);
    return clone(record);
  }

  project(projectUid) {
    const value = this._projects.get(projectUid);
    return value ? clone(value) : null;
  }

  projectByKey(key) {
    const target = String(key).normalize("NFC");
    return [...this._projects.values()].filter((item) => item.key === target).map(clone)[0] ?? null;
  }

  relation(relationUid) {
    const value = this._relations.get(relationUid);
    return value ? clone(value) : null;
  }

  relationsFrom(projectUid) {
    return [...this._relations.values()].filter((item) => item.from_project_uid === projectUid).map(clone);
  }

  relationsTo(projectUid) {
    return [...this._relations.values()].filter((item) => item.to_project_uid === projectUid).map(clone);
  }

  worktree(worktreeUid) {
    const value = this._worktrees.get(worktreeUid);
    return value ? clone(value) : null;
  }

  worktreesFor(projectUid) {
    return [...this._worktrees.values()].filter((item) => item.project_uid === projectUid).map(clone);
  }

  resolveCanonicalPath(projectUid, path) {
    const project = this._projects.get(projectUid);
    if (!project) throw new Error(`unknown project: ${projectUid}`);
    return `${project.project_uid}:${normalizeRelativePath(path)}`;
  }

  resolveRoot(projectUid) {
    const project = this._projects.get(projectUid);
    if (!project) throw new Error(`unknown project: ${projectUid}`);
    return project.root;
  }

  toRecord() {
    return clone({
      schema_version: this.schema_version,
      workspace_uid: this.workspace_uid,
      root: this.root,
      projects: [...this._projects.values()].sort((a, b) => a.project_uid.localeCompare(b.project_uid)),
      relations: [...this._relations.values()].sort((a, b) => a.relation_uid.localeCompare(b.relation_uid)),
      worktrees: [...this._worktrees.values()].sort((a, b) => a.worktree_uid.localeCompare(b.worktree_uid))
    });
  }

  toJSON() {
    return canonicalJson(this.toRecord());
  }

  save(filePath) {
    const target = canonicalRoot(String(filePath));
    mkdirSync(dirname(target), { recursive: true });
    const temporary = `${target}.tmp-${process.pid}-${Date.now()}`;
    writeFileSync(temporary, `${this.toJSON()}\n`, { encoding: "utf8", flag: "wx" });
    renameSync(temporary, target);
    return target;
  }

  static fromRecord(record) {
    if (!record || typeof record !== "object") throw new TypeError("registry record must be an object");
    const registry = new WorkspaceRegistry({ workspaceUid: record.workspace_uid, root: record.root, schemaVersion: record.schema_version });
    for (const project of record.projects ?? []) registry.registerProject(project);
    for (const relation of record.relations ?? []) registry.registerRelation(relation);
    for (const worktree of record.worktrees ?? []) registry.registerWorktree(worktree);
    return registry;
  }

  static load(filePath) {
    return WorkspaceRegistry.fromRecord(JSON.parse(readFileSync(filePath, "utf8")));
  }
}

export function createWorkspaceRegistry(options) {
  return new WorkspaceRegistry(options);
}

export function registryRecord(registry) {
  if (!registry || typeof registry.toRecord !== "function") throw new TypeError("registry must be a WorkspaceRegistry");
  return registry.toRecord();
}
