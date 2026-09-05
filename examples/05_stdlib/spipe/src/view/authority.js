import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";
import { ImmutableSnapshotStore } from "../storage/snapshot_store.js";
import { WorkspaceRegistry } from "../workspace/registry.js";

const AUTHORITY_PORTS = new WeakSet();
const AUTHORITY_VIEWS = new WeakMap();
const CANONICAL_TARGETS = new WeakMap();
const CANDIDATES = new WeakMap();
const DIRECTORY_TARGETS = new WeakMap();
const SCOPE_KINDS = new Set(["project", "workspace_aggregate"]);
const TARGET_KINDS = new Set(["artifact", "section", "aggregate"]);

function fail() { return Object.freeze({ ok: false, error: "SPK-W5A-DENIED" }); }
function ok(value) { return Object.freeze({ ok: true, value }); }
function text(value, field) {
  if (typeof value !== "string" || value.length === 0) throw new TypeError(`${field} is required`);
  return value.normalize("NFC");
}
function nullableText(value, field) { return value === null ? null : text(value, field); }
function digest(value) { return sha256Hex(canonicalJson(value)); }
function normalizedPath(value) {
  const path = text(value, "normalizedLogicalPath").replaceAll("\\", "/");
  if (path.startsWith("/") || path.split("/").some((part) => !part || part === "." || part === "..")) throw new TypeError("logical path is not normalized");
  return path;
}
function binding(input) {
  if (!input || typeof input !== "object" || Array.isArray(input)) throw new TypeError("authority binding is required");
  return freezeDeep({
    workspaceUid: text(input.workspaceUid ?? input.workspace_uid, "workspaceUid"),
    projectUidOrNull: nullableText(input.projectUidOrNull ?? input.project_uid ?? null, "projectUidOrNull"),
    worktreeUid: text(input.worktreeUid ?? input.worktree_uid, "worktreeUid"),
    snapshotUid: text(input.snapshotUid ?? input.snapshot_uid, "snapshotUid"),
    revisionId: text(input.revisionId ?? input.revision_id, "revisionId")
  });
}
function sameBinding(left, right) { return canonicalJson(left) === canonicalJson(right); }
function contributor(record) {
  if (!record || typeof record !== "object") throw new TypeError("aggregate contributor must be an object");
  return freezeDeep({ projectUid: text(record.projectUid ?? record.project_uid, "contributor.projectUid"), baseSnapshotUid: text(record.baseSnapshotUid ?? record.base_snapshot_uid, "contributor.baseSnapshotUid"), authoritySnapshotUid: text(record.authoritySnapshotUid ?? record.authority_snapshot_uid, "contributor.authoritySnapshotUid"), targetInventoryRoot: text(record.targetInventoryRoot ?? record.target_inventory_root, "contributor.targetInventoryRoot") });
}
function compareContributor(a, b) { return a.projectUid.localeCompare(b.projectUid); }
function entry(input) {
  if (!input || typeof input !== "object") throw new TypeError("inventory entry must be an object");
  const kind = text(input.targetKind ?? input.target_kind, "targetKind");
  if (!TARGET_KINDS.has(kind)) throw new TypeError("target kind is invalid");
  const uid = text(input.targetUid ?? input.target_uid, "targetUid");
  return freezeDeep({ targetKind: kind, targetUid: uid, logicalPath: normalizedPath(input.logicalPath ?? input.logical_path), title: text(input.title ?? uid, "entry.title"), content: String(input.content ?? ""), directoryPath: normalizedPath(input.directoryPath ?? input.directory_path ?? input.logicalPath ?? input.logical_path), sortKey: text(input.sortKey ?? input.sort_key ?? `${kind}:${uid}`, "entry.sortKey") });
}
function inventoryPayload(input) {
  const scopeKind = text(input.scopeKind ?? input.scope_kind, "scopeKind");
  if (!SCOPE_KINDS.has(scopeKind)) throw new TypeError("scope kind is invalid");
  const projectUidOrNull = input.projectUidOrNull ?? input.project_uid ?? null;
  const contributors = (input.contributingProjectRoots ?? input.contributing_project_roots ?? []).map(contributor);
  const sorted = [...contributors].sort(compareContributor);
  if (scopeKind === "project" && (projectUidOrNull === null || contributors.length !== 0)) throw new TypeError("project inventory scope is invalid");
  if (scopeKind === "workspace_aggregate" && (projectUidOrNull !== null || contributors.length === 0 || canonicalJson(contributors) !== canonicalJson(sorted))) throw new TypeError("aggregate inventory contributors are invalid");
  const entries = (input.entries ?? []).map(entry).sort((a, b) => `${a.targetKind}\0${a.targetUid}`.localeCompare(`${b.targetKind}\0${b.targetUid}`));
  const keys = new Set();
  for (const item of entries) { const key = `${item.targetKind}\0${item.targetUid}`; if (keys.has(key)) throw new TypeError("duplicate inventory target"); keys.add(key); }
  const rawAliases = input.aliasIndex ?? input.alias_index ?? {};
  const aliases = (Array.isArray(rawAliases) ? rawAliases : Object.entries(rawAliases)).map(([alias, value]) => [text(alias, "alias"), freezeDeep({ targetKind: text(value.targetKind ?? value.target_kind, "alias target kind"), targetUid: text(value.targetUid ?? value.target_uid, "alias target uid") })]).sort(([a], [b]) => a.localeCompare(b));
  const directories = (input.directories ?? []).map((item) => freezeDeep({ viewKind: text(item.viewKind ?? item.view_kind, "directory.viewKind"), logicalPath: normalizedPath(item.logicalPath ?? item.logical_path), selectorDigest: text(item.selectorDigest ?? item.selector_digest, "directory.selectorDigest") })).sort((a, b) => canonicalJson(a).localeCompare(canonicalJson(b)));
  const core = { version: 1, scopeKind, workspaceUid: text(input.workspaceUid ?? input.workspace_uid, "workspaceUid"), projectUidOrNull: projectUidOrNull === null ? null : text(projectUidOrNull, "projectUidOrNull"), worktreeUid: text(input.worktreeUid ?? input.worktree_uid, "worktreeUid"), baseSnapshotUid: text(input.baseSnapshotUid ?? input.base_snapshot_uid, "baseSnapshotUid"), revisionId: text(input.revisionId ?? input.revision_id, "revisionId"), entries, aliasIndex: aliases, directories, projectionRoot: text(input.projectionRoot ?? input.projection_root ?? digest(entries), "projectionRoot"), contributingProjectRoots: sorted };
  const rootDigest = digest(core);
  return freezeDeep({ ...core, rootDigest });
}
function authorityPayload(inventory) {
  const core = { version: 1, scopeKind: inventory.scopeKind, workspaceUid: inventory.workspaceUid, projectUidOrNull: inventory.projectUidOrNull, worktreeUid: inventory.worktreeUid, baseSnapshotUid: inventory.baseSnapshotUid, revisionId: inventory.revisionId, targetInventoryRoot: inventory.rootDigest, contributingProjectRoots: inventory.contributingProjectRoots };
  return freezeDeep({ ...core, snapshotUid: `spka1-${digest(core)}` });
}
function verifyRecord(record) {
  try {
    const inventory = inventoryPayload(record.inventory);
    const authority = authorityPayload(inventory);
    if (canonicalJson(inventory) !== canonicalJson(record.inventory) || canonicalJson(authority) !== canonicalJson(record.authority)) return null;
    return freezeDeep({ inventory, authority });
  } catch { return null; }
}
function atomic(path, bytes) { mkdirSync(dirname(path), { recursive: true }); const temp = `${path}.tmp-${process.pid}-${Date.now()}`; writeFileSync(temp, bytes, { encoding: "utf8", flag: "wx" }); renameSync(temp, path); }

/** Durable, content-addressed authority manifests selected only by exact tuple. */
export class AuthorityManifestStoreV1 {
  constructor({ root }) { this.root = text(root, "root"); mkdirSync(this.root, { recursive: true }); }
  pathFor(snapshotUid) { const uid = text(snapshotUid, "snapshotUid"); if (!/^spka1-[0-9a-f]{64}$/.test(uid)) throw new TypeError("authority snapshot UID is invalid"); return join(this.root, `${uid}.json`); }
  put(inventoryInput) { const inventory = inventoryPayload(inventoryInput); const authority = authorityPayload(inventory); const record = freezeDeep({ inventory, authority }); const path = this.pathFor(authority.snapshotUid); const bytes = `${canonicalJson(record)}\n`; if (existsSync(path)) { if (readFileSync(path, "utf8") !== bytes) throw new Error("immutable authority collision"); } else atomic(path, bytes); return record; }
  get(snapshotUid) { try { const record = JSON.parse(readFileSync(this.pathFor(snapshotUid), "utf8")); return verifyRecord(record); } catch { return null; } }
  select(exactBinding) { const wanted = binding(exactBinding); const record = this.get(wanted.snapshotUid); if (!record) return null; const actual = freezeDeep({ workspaceUid: record.authority.workspaceUid, projectUidOrNull: record.authority.projectUidOrNull, worktreeUid: record.authority.worktreeUid, snapshotUid: record.authority.snapshotUid, revisionId: record.authority.revisionId }); return sameBinding(actual, wanted) ? record : null; }
}

/** Builds sealed manifests from compiler inventory without repository scans. */
export class AuthorityPublisherV1 {
  constructor({ store, snapshotStore, registry }) { if (!(store instanceof AuthorityManifestStoreV1) || !(snapshotStore instanceof ImmutableSnapshotStore) || !(registry instanceof WorkspaceRegistry)) throw new TypeError("AuthorityPublisherV1 requires durable authority/snapshot stores and WorkspaceRegistry"); this.store = store; this.snapshotStore = snapshotStore; this.registry = registry; }
  publishProject({ workspaceUid, inventory, aliases = {}, projectionRoot = null }) {
    if (!inventory?.snapshot) throw new TypeError("compiler inventory is required");
    const contentByPath = new Map((inventory.source_inputs ?? []).map((source) => [source.path, source.content]));
    const artifactPath = new Map((inventory.artifacts ?? []).map((artifact) => [artifact.uid, artifact.canonical_path]));
    const entries = [
      ...(inventory.artifacts ?? []).map((artifact) => ({ targetKind: "artifact", targetUid: artifact.uid, logicalPath: `artifact/${artifact.uid}`, directoryPath: "lifecycle", title: artifact.title, content: contentByPath.get(artifact.canonical_path) ?? "", sortKey: `artifact:${artifact.uid}` })),
      ...(inventory.sections ?? []).map((section) => ({ targetKind: "section", targetUid: section.uid, logicalPath: `section/${section.uid}`, directoryPath: "lifecycle", title: section.title ?? section.key ?? section.uid, content: contentByPath.get(artifactPath.get(section.artifact_uid)) ?? "", sortKey: `section:${section.uid}` }))
    ];
    this.snapshotStore.put(inventory.snapshot);
    const project = this.registry.project(inventory.snapshot.project_uid); const worktree = this.registry.worktree(inventory.snapshot.worktree_uid);
    if (this.registry.workspace_uid !== workspaceUid || !project || !worktree || worktree.project_uid !== project.uid || project.revision !== inventory.snapshot.revision_id || worktree.revision_id !== inventory.snapshot.revision_id) throw new TypeError("publisher tuple is not registry-selected");
    const directories = [{ viewKind: "lifecycle", logicalPath: "lifecycle", selectorDigest: digest({ viewKind: "lifecycle", logicalPath: "lifecycle" }) }];
    return this.store.put({ scopeKind: "project", workspaceUid, projectUidOrNull: inventory.snapshot.project_uid, worktreeUid: inventory.snapshot.worktree_uid, baseSnapshotUid: inventory.snapshot.snapshot_uid, revisionId: inventory.snapshot.revision_id, entries, aliasIndex: aliases, directories, projectionRoot: projectionRoot ?? digest(entries) });
  }
  publishAggregate({ workspaceUid, worktreeUid, revisionId, entries, contributors, aliases = {}, projectionRoot = null }) {
    if (!Array.isArray(contributors)) throw new TypeError("aggregate contributors are required");
    const normalized = contributors.map(contributor); const expectedProjectUids = this.registry.toRecord().projects.filter((project) => project.revision === revisionId).map((project) => project.uid).sort();
    if (this.registry.workspace_uid !== workspaceUid || !this.registry.worktree(worktreeUid) || canonicalJson(normalized) !== canonicalJson([...normalized].sort(compareContributor)) || canonicalJson(normalized.map((item) => item.projectUid)) !== canonicalJson(expectedProjectUids)) throw new TypeError("aggregate contributors do not match durable workspace selection");
    for (const item of normalized) {
      const child = this.store.get(item.authoritySnapshotUid);
      if (!child || child.inventory.workspaceUid !== workspaceUid || child.inventory.worktreeUid !== worktreeUid || child.inventory.revisionId !== revisionId || child.inventory.projectUidOrNull !== item.projectUid || child.inventory.baseSnapshotUid !== item.baseSnapshotUid || child.inventory.rootDigest !== item.targetInventoryRoot) throw new TypeError("aggregate contributor root is unavailable");
    }
    const directories = [{ viewKind: "lifecycle", logicalPath: "root", selectorDigest: digest({ viewKind: "lifecycle", logicalPath: "root" }) }];
    return this.store.put({ scopeKind: "workspace_aggregate", workspaceUid, projectUidOrNull: null, worktreeUid, baseSnapshotUid: `aggregate-${digest(normalized)}`, revisionId, entries, contributingProjectRoots: normalized, aliasIndex: aliases, directories, projectionRoot: projectionRoot ?? digest(entries) });
  }
}

export class SnapshotAuthorityPortV1 {
  #store; #snapshotStore; #registry; #instance;
  constructor({ store, snapshotStore, registry }) { if (!(store instanceof AuthorityManifestStoreV1) || !(snapshotStore instanceof ImmutableSnapshotStore) || !(registry instanceof WorkspaceRegistry)) throw new TypeError("SnapshotAuthorityPortV1 requires durable authority/snapshot stores and WorkspaceRegistry"); this.#store = store; this.#snapshotStore = snapshotStore; this.#registry = registry; this.#instance = {}; AUTHORITY_PORTS.add(this); }
  #baseMatches(record) {
    if (record.inventory.scopeKind === "workspace_aggregate") return record.inventory.contributingProjectRoots.every((item) => {
      const child = this.#store.get(item.authoritySnapshotUid);
      return child && child.inventory.rootDigest === item.targetInventoryRoot && child.inventory.baseSnapshotUid === item.baseSnapshotUid && child.inventory.projectUidOrNull === item.projectUid;
    });
    try { const base = this.#snapshotStore.get(record.inventory.baseSnapshotUid); return base.project_uid === record.inventory.projectUidOrNull && base.worktree_uid === record.inventory.worktreeUid && base.revision_id === record.inventory.revisionId; } catch { return false; }
  }
  #registryMatches(exact) { if (this.#registry.workspace_uid !== exact.workspaceUid) return false; const worktree = this.#registry.worktree(exact.worktreeUid); if (!worktree || worktree.revision_id !== exact.revisionId) return false; if (exact.projectUidOrNull === null) return true; const project = this.#registry.project(exact.projectUidOrNull); return Boolean(project) && project.revision === exact.revisionId && worktree.project_uid === exact.projectUidOrNull; }
  openBoundSnapshot(value) { const exact = binding(value); const record = this.#store.select(exact); if (!record || !this.#registryMatches(exact) || !this.#baseMatches(record)) return fail(); const view = freezeDeep({ binding: exact, manifestDigest: record.inventory.rootDigest, authoritySnapshotUid: record.authority.snapshotUid }); AUTHORITY_VIEWS.set(view, this.#instance); return ok(view); }
  #record(view) { if (!view || AUTHORITY_VIEWS.get(view) !== this.#instance) return null; const record = this.#store.select(view.binding); if (!record || record.inventory.rootDigest !== view.manifestDigest || !this.#baseMatches(record)) return null; return record; }
  resolveCanonicalTarget(view, value) { const record = this.#record(view); if (!record) return fail(); const candidate = value && CANDIDATES.get(value); if (candidate && (candidate.instance !== this.#instance || canonicalJson(candidate.binding) !== canonicalJson(view.binding) || candidate.manifestDigest !== view.manifestDigest)) return fail(); const kind = value?.targetKind ?? value?.target_kind; const uid = value?.targetUid ?? value?.target_uid; const found = record.inventory.entries.find((item) => item.targetKind === kind && item.targetUid === uid); if (!found) return fail(); const target = freezeDeep({ binding: view.binding, manifestDigest: view.manifestDigest, targetKind: found.targetKind, targetUid: found.targetUid, logicalPath: found.logicalPath }); CANONICAL_TARGETS.set(target, this.#instance); return ok(target); }
  resolveCanonicalAlias(view, value) { const record = this.#record(view); if (!record) return fail(); const alias = value?.normalizedAliasUri ?? value?.normalized_alias_uri; if (typeof alias !== "string") return fail(); const matches = record.inventory.aliasIndex.filter(([key]) => key === alias); if (matches.length !== 1) return fail(); const [, found] = matches[0]; const candidate = freezeDeep({ targetKind: found.targetKind, targetUid: found.targetUid, aliasIndexDigest: digest(record.inventory.aliasIndex) }); CANDIDATES.set(candidate, { instance: this.#instance, binding: view.binding, manifestDigest: view.manifestDigest }); return ok(candidate); }
  listDirectoryTarget(view, value) { const record = this.#record(view); if (!record) return fail(); try { const viewKind = text(value?.viewKind ?? value?.view_kind, "viewKind"); const logicalPath = normalizedPath(value?.normalizedLogicalPath ?? value?.normalized_logical_path); const selectorDigest = text(value?.selectorDigest ?? value?.selector_digest, "selectorDigest"); const sealed = record.inventory.directories.find((item) => item.viewKind === viewKind && item.logicalPath === logicalPath && item.selectorDigest === selectorDigest); if (!sealed) return fail(); const directory = freezeDeep({ binding: view.binding, manifestDigest: view.manifestDigest, viewKind, logicalPath, selectorDigest }); DIRECTORY_TARGETS.set(directory, this.#instance); return ok(directory); } catch { return fail(); } }
  isTarget(value) { return CANONICAL_TARGETS.get(value) === this.#instance; }
  isDirectory(value) { return DIRECTORY_TARGETS.get(value) === this.#instance; }
  recordFor(view) { return this.#record(view); }
}

export function isSnapshotAuthorityPortV1(value) { return AUTHORITY_PORTS.has(value); }
export function authorityManifestDigest(input) { return inventoryPayload(input).rootDigest; }
