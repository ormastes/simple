import { createHash } from "node:crypto";

import { canonicalJson, freezeDeep, sha256Hex } from "./canonical.js";
import { assertCanonicalUid, normalizeHash, normalizeRevision, normalizeText } from "../model/identity.js";

const TARGET_KINDS = Object.freeze(["artifact", "section", "aggregate", "directory"]);
const SCOPE_KINDS = Object.freeze(["project", "workspace_aggregate"]);
const STORES = new WeakSet();

function hash(value) { return `sha256:${sha256Hex(canonicalJson(value))}`; }
function uid(value, field, prefixes) { return assertCanonicalUid(value, field, prefixes); }
function sortByJson(values) { return [...values].sort((a, b) => canonicalJson(a).localeCompare(canonicalJson(b))); }
function targetUid(value, kind, field) {
  if (kind === "artifact") return uid(value, field, ["A"]);
  if (kind === "section") return uid(value, field, ["S"]);
  return normalizeText(value, field);
}
function normalizeContributors(value, scopeKind) {
  if (scopeKind === "project") {
    if (value !== undefined && (!Array.isArray(value) || value.length !== 0)) throw new TypeError("project inventory forbids contributing_project_roots");
    return Object.freeze([]);
  }
  if (!Array.isArray(value)) throw new TypeError("workspace aggregate requires contributing_project_roots");
  const records = value.map((item) => {
    if (!item || typeof item !== "object" || Array.isArray(item)) throw new TypeError("contributor must be an object");
    return freezeDeep({
      project_uid: uid(item.project_uid ?? item.projectUid, "contributor.project_uid", ["P"]),
      base_snapshot_uid: normalizeText(item.base_snapshot_uid ?? item.baseSnapshotUid, "contributor.base_snapshot_uid"),
      authority_snapshot_uid: normalizeText(item.authority_snapshot_uid ?? item.authoritySnapshotUid, "contributor.authority_snapshot_uid"),
      target_inventory_root: normalizeHash(item.target_inventory_root ?? item.targetInventoryRoot, "contributor.target_inventory_root")
    });
  });
  for (let i = 1; i < records.length; i += 1) if (records[i - 1].project_uid.localeCompare(records[i].project_uid) >= 0) throw new TypeError("contributing_project_roots must be strictly project-UID ordered");
  return Object.freeze(records);
}
function normalizedEntries(value) {
  if (!Array.isArray(value)) throw new TypeError("inventory entries must be an array");
  const entries = value.map((item) => {
    if (!item || typeof item !== "object" || Array.isArray(item)) throw new TypeError("inventory entry must be an object");
    const target_kind = normalizeText(item.target_kind ?? item.targetKind, "entry.target_kind");
    if (!TARGET_KINDS.includes(target_kind)) throw new TypeError("entry.target_kind is invalid");
    return freezeDeep({
      target_kind,
      target_uid: targetUid(item.target_uid ?? item.targetUid, target_kind, "entry.target_uid"),
      locator: normalizeText(item.locator ?? item.target_uid ?? item.targetUid, "entry.locator"),
      content_digest: normalizeHash(item.content_digest ?? item.contentDigest, "entry.content_digest"),
      view_kind: item.view_kind == null ? null : normalizeText(item.view_kind, "entry.view_kind"),
      logical_path: item.logical_path == null ? null : normalizeText(item.logical_path, "entry.logical_path"),
      selector_digest: item.selector_digest == null ? null : normalizeHash(item.selector_digest, "entry.selector_digest"),
      children: Object.freeze((item.children ?? []).map((child) => ({ target_kind: normalizeText(child.target_kind ?? child.targetKind, "child.target_kind"), target_uid: normalizeText(child.target_uid ?? child.targetUid, "child.target_uid") })).sort((a, b) => canonicalJson(a).localeCompare(canonicalJson(b))))
    });
  });
  const sorted = sortByJson(entries);
  const seenTargets = new Set(); for (const entry of sorted) { const key = `${entry.target_kind}\0${entry.target_uid}`; if (seenTargets.has(key)) throw new TypeError("inventory target is duplicated"); seenTargets.add(key); }
  return Object.freeze(sorted);
}
function normalizedAliases(value) {
  if (!Array.isArray(value)) throw new TypeError("alias_index must be an array");
  const aliases = value.map((item) => {
    const normalized_alias_uri = normalizeText(item.normalized_alias_uri ?? item.normalizedAliasUri, "alias.normalized_alias_uri");
    const target_kind = normalizeText(item.target_kind ?? item.targetKind, "alias.target_kind");
    if (!TARGET_KINDS.includes(target_kind)) throw new TypeError("alias target kind is invalid");
    return freezeDeep({ normalized_alias_uri, target_kind, target_uid: targetUid(item.target_uid ?? item.targetUid, target_kind, "alias.target_uid") });
  });
  const sorted = sortByJson(aliases);
  for (let i = 1; i < sorted.length; i += 1) if (sorted[i - 1].normalized_alias_uri === sorted[i].normalized_alias_uri) throw new TypeError("alias is ambiguous");
  return Object.freeze(sorted);
}
function inventoryUnsigned(input) {
  const scope_kind = normalizeText(input.scope_kind ?? input.scopeKind, "scope_kind");
  if (!SCOPE_KINDS.includes(scope_kind)) throw new TypeError("scope_kind is invalid");
  const project_uid = input.project_uid ?? input.projectUid ?? null;
  if (scope_kind === "project" && project_uid == null) throw new TypeError("project inventory requires project_uid");
  if (scope_kind === "workspace_aggregate" && project_uid != null) throw new TypeError("workspace aggregate forbids project_uid");
  return {
    version: 1, scope_kind,
    workspace_uid: uid(input.workspace_uid ?? input.workspaceUid, "workspace_uid", ["W"]),
    project_uid: project_uid == null ? null : uid(project_uid, "project_uid", ["P"]),
    worktree_uid: uid(input.worktree_uid ?? input.worktreeUid, "worktree_uid", ["W"]),
    base_snapshot_uid: normalizeText(input.base_snapshot_uid ?? input.baseSnapshotUid, "base_snapshot_uid"),
    revision_id: normalizeRevision(input.revision_id ?? input.revisionId, "revision_id"),
    entries: normalizedEntries(input.entries), alias_index: normalizedAliases(input.alias_index ?? input.aliasIndex ?? []),
    projection_root: normalizeHash(input.projection_root ?? input.projectionRoot, "projection_root"),
    contributing_project_roots: normalizeContributors(input.contributing_project_roots ?? input.contributingProjectRoots, scope_kind)
  };
}
export function createTargetInventoryManifestV1(input) {
  const value = inventoryUnsigned(input);
  const root_digest = hash(value);
  if (input.root_digest !== undefined && normalizeHash(input.root_digest, "root_digest") !== root_digest) throw new TypeError("target inventory root digest mismatch");
  return freezeDeep({ ...value, root_digest });
}
export function targetAliasIndexDigestV1(aliases) { return hash(normalizedAliases(aliases)); }
export function createAuthorityManifestV1(input) {
  const inventory = createTargetInventoryManifestV1(input.inventory ?? input);
  const value = {
    version: 1, base_snapshot_uid: inventory.base_snapshot_uid, target_inventory_root: inventory.root_digest,
    workspace_uid: inventory.workspace_uid, project_uid: inventory.project_uid, worktree_uid: inventory.worktree_uid,
    revision_id: inventory.revision_id, scope_kind: inventory.scope_kind,
    contributing_project_roots: inventory.contributing_project_roots
  };
  const snapshot_uid = `spka1-${createHash("sha256").update(canonicalJson(value)).digest("hex")}`;
  if (input.snapshot_uid !== undefined && input.snapshot_uid !== snapshot_uid) throw new TypeError("authority snapshot UID mismatch");
  return freezeDeep({ ...value, snapshot_uid });
}
export class TargetInventoryStore {
  constructor() { this._records = new Map(); STORES.add(this); }
  put(input) {
    const inventory = createTargetInventoryManifestV1(input.inventory ?? input);
    const authority = createAuthorityManifestV1({ inventory, snapshot_uid: input.authority?.snapshot_uid ?? input.snapshot_uid });
    const record = freezeDeep({ inventory, authority });
    const existing = this._records.get(authority.snapshot_uid);
    if (existing && canonicalJson(existing) !== canonicalJson(record)) throw new Error("authority inventory collision");
    this._records.set(authority.snapshot_uid, record); return record;
  }
  get(snapshotUid) { return this._records.get(snapshotUid) ?? null; }
}
export function isTargetInventoryStore(value) { return STORES.has(value); }
