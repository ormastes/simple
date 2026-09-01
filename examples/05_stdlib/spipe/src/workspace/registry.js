import { existsSync } from "node:fs";
import { join, relative } from "node:path";

import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";
import { createProjectRelation, relationKey } from "./linked_project.js";
import { canonicalRoot, normalizeRelativePath } from "./paths.js";
import { createWorktreeRecord } from "./worktree.js";
import { opaqueUid } from "../core/identity.js";
import { createProjectRecord } from "../model/project.js";
import { assertCanonicalUid } from "../model/identity.js";

const WORKSPACE_REGISTRY_V1_BRAND = new WeakSet();

/** Internal construction brand; prototype/instanceof lookalikes are not owners. */
export function isWorkspaceRegistryV1(value) {
  return WORKSPACE_REGISTRY_V1_BRAND.has(value);
}

function clone(value) {
  return JSON.parse(canonicalJson(value));
}

function projectRecord(input, workspaceUid, workspaceRoot) {
  if (!input || typeof input !== "object") throw new TypeError("project must be an object");
  const key = String(input.key ?? input.projectKey ?? input.name ?? "").normalize("NFC");
  if (!key || !/^[A-Za-z0-9][A-Za-z0-9._~-]*$/.test(key)) throw new TypeError("project key is invalid");
  const projectRoot = input.host_root ?? input.root ?? input.projectRoot;
  if (typeof projectRoot !== "string" || projectRoot.length === 0) throw new TypeError("project root is required");
  const root = canonicalRoot(projectRoot);
  const uid = input.projectUid ?? input.project_uid ?? input.uid ?? opaqueUid("P");
  assertCanonicalUid(uid, "project UID", ["P"]);
  const revision = input.revisionId ?? input.revision_id ?? input.revision;
  if (!revision) throw new TypeError("project resolved revision is required");
  const contained = root === workspaceRoot || root.startsWith(`${workspaceRoot}/`);
  const logicalRoot = contained ? (relative(workspaceRoot, root).replaceAll("\\", "/") || ".") : ".";
  const model = createProjectRecord({
    uid,
    key,
    title: input.title ?? key,
    root_path: input.root_path ?? logicalRoot,
    revision: String(revision),
    trust_scope: input.trust_scope ?? "untrusted_data",
    visibility: input.visibility ?? "project",
    status: input.status ?? "active",
    aliases: input.aliases ?? [],
    metadata_hash: input.metadata_hash ?? null
  });
  return freezeDeep(clone({ ...model, host_root: root }));
}

/**
 * Registry for one workspace.  It stores identity and relationship metadata;
 * it never infers semantic dependency from a path, symlink, gitlink, or
 * worktree mount.
 */
export class WorkspaceRegistry {
  constructor({
    workspaceUid = null, workspace_id = null, workspaceId = null, root,
    schemaVersion = 1, persistencePort = null, resolutionAuthorizer = null
  } = {}) {
    if (typeof root !== "string" || root.length === 0) throw new TypeError("workspace root is required");
    this.workspace_uid = workspaceUid ?? workspace_id ?? workspaceId ?? opaqueUid("W");
    assertCanonicalUid(this.workspace_uid, "workspace UID", ["W"]);
    this.root = canonicalRoot(String(root ?? ""));
    this.schema_version = schemaVersion;
    this.persistence_port = persistencePort;
    this.resolution_authorizer = resolutionAuthorizer;
    this._projects = new Map();
    this._relations = new Map();
    this._worktrees = new Map();
    WORKSPACE_REGISTRY_V1_BRAND.add(this);
  }

  registerProject(input) {
    const record = projectRecord(input, this.workspace_uid, this.root);
    const prior = this._projects.get(record.uid);
    if (prior) {
      if (canonicalJson(prior) !== canonicalJson(record)) throw new Error(`project UID already names different metadata: ${record.project_uid}`);
      return clone(prior);
    }
    for (const existing of this._projects.values()) {
      if (existing.key === record.key) throw new Error(`project key already registered: ${record.key}`);
    }
    this._projects.set(record.uid, record);
    return clone(record);
  }

  registerRelation(input) {
    const relation = createProjectRelation(input);
    if (!this._projects.has(relation.from_project_uid) || !this._projects.has(relation.to_project_uid)) {
      throw new Error("both relation endpoints must be registered projects");
    }
    const existingUid = this._relations.get(relation.relation_uid);
    if (existingUid && relationKey(existingUid) !== relationKey(relation)) {
      throw new Error(`relation UID already names a different relation: ${relation.relation_uid}`);
    }
    const key = relationKey(relation);
    for (const existing of this._relations.values()) {
      if (relationKey(existing) === key) return clone(existing);
    }
    this._relations.set(relation.relation_uid, relation);
    return clone(relation);
  }

  registerLinkedProject(input) {
    return this.registerRelation(input);
  }

  registerLink(input) {
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

  /** Composition-root selection of the one authority snapshot for an exact scope tuple. */
  registerAuthoritySnapshot(input) {
    if (!input || typeof input !== "object" || Array.isArray(input)) throw new TypeError("authority snapshot selection must be an object");
    const workspace_uid = input.workspace_uid ?? input.workspaceUid ?? this.workspace_uid;
    if (workspace_uid !== this.workspace_uid) throw new Error("authority snapshot workspace does not match registry");
    const project_uid = input.project_uid ?? input.projectUid ?? input.projectUidOrNull ?? null;
    if (project_uid !== null) assertCanonicalUid(project_uid, "authority project UID", ["P"]);
    const worktree_uid = input.worktree_uid ?? input.worktreeUid;
    assertCanonicalUid(worktree_uid, "authority worktree UID", ["W"]);
    const worktree = this._worktrees.get(worktree_uid);
    if (!worktree || (project_uid !== null && worktree.project_uid !== project_uid)) throw new Error("authority snapshot scope is not registered");
    const revision_id = String(input.revision_id ?? input.revisionId ?? "");
    const snapshot_uid = String(input.snapshot_uid ?? input.snapshotUid ?? "");
    if (!revision_id || !snapshot_uid) throw new TypeError("authority snapshot revision and UID are required");
    const key = canonicalJson({ workspace_uid, project_uid, worktree_uid, revision_id });
    const prior = this._authoritySnapshots.get(key);
    if (prior && prior !== snapshot_uid) throw new Error("authority snapshot scope already has a different selected snapshot");
    this._authoritySnapshots.set(key, snapshot_uid);
    return snapshot_uid;
  }

  authoritySnapshot(input) {
    if (!input || typeof input !== "object") return null;
    const key = canonicalJson({ workspace_uid: input.workspace_uid ?? input.workspaceUid, project_uid: input.project_uid ?? input.projectUid ?? input.projectUidOrNull ?? null, worktree_uid: input.worktree_uid ?? input.worktreeUid, revision_id: input.revision_id ?? input.revisionId });
    return this._authoritySnapshots.get(key) ?? null;
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
    return `${project.uid}:${normalizeRelativePath(path)}`;
  }

  resolveRoot(projectUid) {
    const project = this._projects.get(projectUid);
    if (!project) throw new Error(`unknown project: ${projectUid}`);
    return project.host_root;
  }

  resolveLinkedProject(relationUid, { expectedRevision = null, allowedTrust = ["trusted", "reviewed"] } = {}) {
    const unavailable = (reason, details = {}) => ({
      status: "unavailable",
      diagnostic: { code: "SPK103", severity: "error", message_key: `linked_project.${reason}`, details: { relation_uid: relationUid, ...details } }
    });
    if (typeof this.resolution_authorizer !== "function" || this.resolution_authorizer({
      workspace_root: this.root, requested_relation_uid: relationUid
    }) !== true) return unavailable("authorization_denied");
    const relation = this._relations.get(relationUid);
    if (!relation) return unavailable("relation_missing");
    const project = this._projects.get(relation.to_project_uid);
    if (!project) return unavailable("project_missing", { project_uid: relation.to_project_uid });
    if (!existsSync(project.host_root)) return unavailable("root_unavailable", { project_uid: project.uid });
    const requiredRevision = expectedRevision ?? relation.revision;
    if (requiredRevision !== null && project.revision !== requiredRevision) {
      return unavailable("revision_mismatch", { project_uid: project.uid, expected_revision: requiredRevision, actual_revision: project.revision });
    }
    if (!allowedTrust.includes(relation.trust)) return unavailable("trust_denied", { project_uid: project.uid, trust: relation.trust });
    const fromProject = this._projects.get(relation.from_project_uid);
    if (relation.mount !== null) {
      if (!fromProject) return unavailable("source_project_missing", { project_uid: relation.from_project_uid });
      const mountedPath = join(fromProject.host_root, ...relation.mount.split("/"));
      if (!existsSync(mountedPath)) return unavailable("mount_unavailable", { project_uid: project.uid });
      if (canonicalRoot(mountedPath) !== canonicalRoot(project.host_root)) {
        return unavailable("mount_target_mismatch", { project_uid: project.uid });
      }
    }
    return { status: "resolved", project: clone(project), relation: clone(relation) };
  }

  toRecord() {
    return clone({
      schema_version: this.schema_version,
      workspace_uid: this.workspace_uid,
      root: this.root,
      projects: [...this._projects.values()].sort((a, b) => a.uid.localeCompare(b.uid)),
      relations: [...this._relations.values()].sort((a, b) => a.relation_uid.localeCompare(b.relation_uid)),
      worktrees: [...this._worktrees.values()].sort((a, b) => a.worktree_uid.localeCompare(b.worktree_uid))
    });
  }

  toJSON() {
    return canonicalJson(this.toRecord());
  }

  registryRevisionId() {
    return `sha256:${sha256Hex(canonicalJson(this.toRecord()))}`;
  }

  save(relativePath) {
    const normalized = normalizeRelativePath(relativePath);
    if (!this.persistence_port || typeof this.persistence_port.writeRegistry !== "function") {
      throw new Error("SafeRegistryPersistencePort unavailable");
    }
    return this.persistence_port.writeRegistry({
      workspace_root: this.root,
      relative_path: normalized,
      bytes: Buffer.from(`${this.toJSON()}\n`, "utf8")
    });
  }

  static fromRecord(record, { persistencePort = null, trustedWorkspaceRoot = null, resolutionAuthorizer = null } = {}) {
    if (!record || typeof record !== "object") throw new TypeError("registry record must be an object");
    const root = trustedWorkspaceRoot === null ? record.root : canonicalRoot(trustedWorkspaceRoot);
    if (trustedWorkspaceRoot !== null && canonicalRoot(record.root) !== root) {
      throw new Error("persisted registry workspace root does not match trusted workspace root");
    }
    const registry = new WorkspaceRegistry({
      workspaceUid: record.workspace_uid, root,
      schemaVersion: record.schema_version, persistencePort, resolutionAuthorizer
    });
    for (const project of record.projects ?? []) registry.registerProject(project);
    for (const relation of record.relations ?? []) registry.registerRelation(relation);
    for (const worktree of record.worktrees ?? []) registry.registerWorktree(worktree);
    return registry;
  }

  static load({ workspaceRoot, relativePath, persistencePort }) {
    if (!persistencePort || typeof persistencePort.readRegistry !== "function" ||
        typeof persistencePort.authorizeProjectRoot !== "function" ||
        typeof persistencePort.authorizeLinkedProject !== "function") {
      throw new Error("SafeRegistryPersistencePort unavailable");
    }
    const normalized = normalizeRelativePath(relativePath);
    const trustedRoot = canonicalRoot(workspaceRoot);
    const bytes = persistencePort.readRegistry({ workspace_root: trustedRoot, relative_path: normalized });
    const record = JSON.parse(Buffer.from(bytes).toString("utf8"));
    for (const project of record.projects ?? []) {
      if (persistencePort.authorizeProjectRoot({ workspace_root: trustedRoot, project: clone(project) }) !== true) {
        throw new Error("persisted project root is outside the authorized registry scope");
      }
    }
    return WorkspaceRegistry.fromRecord(record, {
      persistencePort, trustedWorkspaceRoot: workspaceRoot,
      resolutionAuthorizer: (request) => persistencePort.authorizeLinkedProject(request)
    });
  }

}

/** Internal composition-root identity; structural lookalikes are not registries. */
export function isWorkspaceRegistryV1(value) { return WORKSPACE_REGISTRIES.has(value); }

export function createWorkspaceRegistry(options) {
  return new WorkspaceRegistry(options);
}

export function isWorkspaceRegistryV1(value) {
  return REGISTRY_V1.has(value);
}

export function registryRecord(registry) {
  if (!registry || typeof registry.toRecord !== "function") throw new TypeError("registry must be a WorkspaceRegistry");
  return registry.toRecord();
}
