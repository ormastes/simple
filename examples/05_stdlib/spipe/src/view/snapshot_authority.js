import { createHash } from "node:crypto";

import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";

const PORTS = new WeakSet();
const VIEWS = new WeakMap();
const TARGETS = new WeakMap();
const DIRECTORIES = new WeakMap();
const BINDINGS = new WeakMap();

const receiptFields = Object.freeze([
  "authorityKeyId", "authorityKeyEpoch", "normalizedAliasUriOrNull", "canonicalUri",
  "workspaceUid", "projectUidOrNull", "targetKind", "targetUid", "snapshotUid",
  "revisionId", "viewKind", "normalizedLogicalPath", "selectorDigest",
  "effectiveScopeDigest", "orderingVersion", "pageLimitOrNull", "policyVersion"
]);

function deny() { return null; }
function exactObject(value, fields) {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const keys = Object.keys(value).sort();
  return keys.length === fields.length && keys.every((key, index) => key === [...fields].sort()[index]);
}
function text(value) { return typeof value === "string" && value.length > 0 && value === value.normalize("NFC"); }
function digest(value) { return sha256Hex(canonicalJson(value)); }
function hash(value) { return typeof value === "string" && /^(?:sha256:)?[0-9a-f]{64}$/.test(value); }
function opaque(value, prefix) { return typeof value === "string" && new RegExp(`^${prefix}-[A-Za-z0-9._~-]+$`).test(value); }
function fixedFields(value) {
  return receiptFields.every((field) => Object.hasOwn(value, field)) &&
    text(value.authorityKeyId) && Number.isSafeInteger(value.authorityKeyEpoch) && value.authorityKeyEpoch >= 0 &&
    (value.normalizedAliasUriOrNull === null || text(value.normalizedAliasUriOrNull)) && text(value.canonicalUri) &&
    opaque(value.workspaceUid, "W") && (value.projectUidOrNull === null || opaque(value.projectUidOrNull, "P")) &&
    text(value.targetKind) && text(value.targetUid) && text(value.snapshotUid) && text(value.revisionId) &&
    text(value.viewKind) && typeof value.normalizedLogicalPath === "string" && hash(value.selectorDigest) &&
    hash(value.effectiveScopeDigest) && text(value.orderingVersion) &&
    (value.pageLimitOrNull === null || (Number.isSafeInteger(value.pageLimitOrNull) && value.pageLimitOrNull > 0)) &&
    text(value.policyVersion);
}
function targetEntry(inventory, kind, uid) {
  return Array.isArray(inventory.entries) ? inventory.entries.find((entry) => entry.targetKind === kind && entry.targetUid === uid) ?? null : null;
}
function authoritySnapshotUid(authority) { return `spka1-${digest({ ...authority, snapshotUid: undefined })}`; }
function validContributor(value) { return exactObject(value, ["projectUid", "baseSnapshotUid", "authoritySnapshotUid", "targetInventoryRoot"]) && opaque(value.projectUid, "P") && text(value.baseSnapshotUid) && text(value.authoritySnapshotUid) && hash(value.targetInventoryRoot); }
function sealedInventory(inventory, authority) {
  if (!exactObject(inventory, ["version", "scopeKind", "workspaceUid", "projectUidOrNull", "worktreeUid", "baseSnapshotUid", "revisionId", "entries", "aliasIndex", "projectionRoot", "contributingProjectRoots", "rootDigest"]) ||
      inventory.version !== "v1" || !Array.isArray(inventory.entries) || !Array.isArray(inventory.contributingProjectRoots) || !hash(inventory.projectionRoot)) return false;
  if (inventory.scopeKind === "project") {
    if (!opaque(inventory.projectUidOrNull, "P") || inventory.contributingProjectRoots.length !== 0) return false;
  } else if (inventory.scopeKind === "workspace_aggregate") {
    if (inventory.projectUidOrNull !== null || !inventory.contributingProjectRoots.every(validContributor)) return false;
  } else return false;
  const contributors = inventory.contributingProjectRoots.map((item) => item.projectUid);
  if (contributors.some((id, index) => index && contributors[index - 1] >= id)) return false;
  const seen = new Set();
  for (const entry of inventory.entries) {
    if (!exactObject(entry, ["targetKind", "targetUid", "locator", "contentDigest"]) || !text(entry.targetKind) || !text(entry.targetUid) || !text(entry.locator) || !hash(entry.contentDigest)) return false;
    const key = `${entry.targetKind}\0${entry.targetUid}`; if (seen.has(key)) return false; seen.add(key);
  }
  const ordered = [...inventory.entries].sort((a, b) => canonicalJson(a).localeCompare(canonicalJson(b)));
  return canonicalJson(ordered) === canonicalJson(inventory.entries) && canonicalJson(inventory.scopeKind === "workspace_aggregate" ? inventory.contributingProjectRoots : []) === canonicalJson(authority.contributingProjectRoots);
}

/**
 * Composition-root capability for an immutable, sealed target inventory.  Its
 * opaque values deliberately cannot be made by URI/MCP adapters.
 */
export function createSnapshotAuthorityPortV1({ workspaceRegistry, snapshotStore, targetInventoryStore, authorityInstanceUid } = {}) {
  if (!workspaceRegistry || !snapshotStore || !targetInventoryStore || !opaque(authorityInstanceUid, "AI")) {
    throw new TypeError("SnapshotAuthorityPortV1 requires trusted stores and an authority instance UID");
  }
  function openBoundSnapshot(binding) {
    try {
      if (!exactObject(binding, ["workspaceUid", "projectUidOrNull", "worktreeUid", "snapshotUid", "revisionId"]) ||
          !opaque(binding.workspaceUid, "W") || !opaque(binding.worktreeUid, "WT") || !text(binding.snapshotUid) || !text(binding.revisionId)) return deny();
      if (binding.workspaceUid !== workspaceRegistry.workspace_uid) return deny();
      const worktree = workspaceRegistry.worktree(binding.worktreeUid);
      if (!worktree || (binding.projectUidOrNull !== null && worktree.project_uid !== binding.projectUidOrNull)) return deny();
      const authority = targetInventoryStore.readAuthorityManifest(binding.snapshotUid);
      if (!authority || !exactObject(authority, ["snapshotUid", "baseSnapshotUid", "targetInventoryRoot", "workspaceUid", "projectUidOrNull", "worktreeUid", "revisionId", "scopeKind", "contributingProjectRoots"])) return deny();
      if (authority.snapshotUid !== binding.snapshotUid || authority.snapshotUid !== authoritySnapshotUid(authority) || authority.workspaceUid !== binding.workspaceUid ||
          authority.projectUidOrNull !== binding.projectUidOrNull || authority.worktreeUid !== binding.worktreeUid || authority.revisionId !== binding.revisionId ||
          !hash(authority.targetInventoryRoot)) return deny();
      const base = snapshotStore.read(authority.baseSnapshotUid);
      if (!base || base.worktree_uid !== binding.worktreeUid || base.revision_id !== binding.revisionId ||
          (binding.projectUidOrNull !== null && base.project_uid !== binding.projectUidOrNull)) return deny();
      const inventory = targetInventoryStore.readTargetInventory(authority.targetInventoryRoot);
      if (!inventory || !sealedInventory(inventory, authority)) return deny();
      const rootDigest = digest({ ...inventory, rootDigest: undefined });
      if (inventory.rootDigest !== rootDigest || inventory.rootDigest !== authority.targetInventoryRoot.replace(/^sha256:/, "") ||
          inventory.workspaceUid !== binding.workspaceUid || inventory.projectUidOrNull !== binding.projectUidOrNull ||
          inventory.worktreeUid !== binding.worktreeUid || inventory.baseSnapshotUid !== authority.baseSnapshotUid || inventory.revisionId !== binding.revisionId ||
          canonicalJson(inventory.contributingProjectRoots) !== canonicalJson(authority.contributingProjectRoots)) return deny();
      const view = Object.freeze({});
      VIEWS.set(view, freezeDeep({ binding: { ...binding }, authorityManifestDigest: digest(authority), inventory, authorityInstanceUid }));
      return view;
    } catch { return deny(); }
  }
  function viewData(view) { return VIEWS.get(view) ?? null; }
  function resolveCanonicalTarget(view, request) {
    const data = viewData(view);
    if (!data || !exactObject(request, ["targetKind", "targetUid"]) || !text(request.targetKind) || !text(request.targetUid)) return deny();
    const entry = targetEntry(data.inventory, request.targetKind, request.targetUid);
    if (!entry) return deny();
    const target = Object.freeze({});
    TARGETS.set(target, freezeDeep({ data, entry }));
    return target;
  }
  function resolveCanonicalAlias(view, request) {
    const data = viewData(view);
    if (!data || !exactObject(request, ["normalizedAliasUri"]) || !text(request.normalizedAliasUri)) return deny();
    const match = data.inventory.aliasIndex?.[request.normalizedAliasUri];
    if (!match || !exactObject(match, ["targetKind", "targetUid"]) || !text(match.targetKind) || !text(match.targetUid)) return deny();
    return freezeDeep({ targetKind: match.targetKind, targetUid: match.targetUid, aliasIndexDigest: digest(data.inventory.aliasIndex) });
  }
  function listDirectoryTarget(view, request) {
    const data = viewData(view);
    if (!data || !exactObject(request, ["viewKind", "normalizedLogicalPath", "selectorDigest"]) || !text(request.viewKind) ||
        typeof request.normalizedLogicalPath !== "string" || !hash(request.selectorDigest)) return deny();
    const entry = targetEntry(data.inventory, "directory", `${request.viewKind}:${request.normalizedLogicalPath}:${request.selectorDigest}`);
    if (!entry) return deny();
    const directory = Object.freeze({}); DIRECTORIES.set(directory, freezeDeep({ data, entry })); return directory;
  }
  function createExpectedReadBindingV1(view, targetOrDirectory, request) {
    const data = viewData(view), object = TARGETS.get(targetOrDirectory) ?? DIRECTORIES.get(targetOrDirectory);
    if (!data || !object || object.data !== data || !exactObject(request, receiptFields)) return deny();
    const expected = { ...request, worktreeUid: data.binding.worktreeUid, authorityInstanceUid, authorityManifestDigest: data.authorityManifestDigest };
    const directory = DIRECTORIES.has(targetOrDirectory);
    if (!fixedFields(expected) || (directory ? expected.pageLimitOrNull === null : expected.pageLimitOrNull !== null) || expected.workspaceUid !== data.binding.workspaceUid || expected.projectUidOrNull !== data.binding.projectUidOrNull ||
        expected.snapshotUid !== data.binding.snapshotUid || expected.revisionId !== data.binding.revisionId ||
        expected.targetKind !== object.entry.targetKind || expected.targetUid !== object.entry.targetUid) return deny();
    const binding = Object.freeze({}); BINDINGS.set(binding, freezeDeep(expected)); return binding;
  }
  const port = Object.freeze({ openBoundSnapshot, resolveCanonicalTarget, resolveCanonicalAlias, listDirectoryTarget, createExpectedReadBindingV1 });
  PORTS.add(port); return port;
}
export function isSnapshotAuthorityPortV1(value) { return PORTS.has(value); }
export function expectedReadBindingClaimsV1(value) { return BINDINGS.get(value) ?? null; }
