/*
 * Wave 5a sealed read authority.  This is intentionally pre-cursor: it
 * publishes and opens immutable, verified views only.  URI, ProjectionPort,
 * MCP and receipt issuance are separate downstream concerns.
 */
import { createHash } from "node:crypto";
import { closeSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { canonicalJson, freezeDeep } from "../storage/canonical.js";
import { isWorkspaceRegistryV1 } from "../workspace/registry.js";
import { isSnapshotStoreV1 } from "../storage/snapshot_store.js";
import { fsyncDirectory } from "../storage/directory_fsync.js";

const PORTS = new WeakSet();
const PERMITS = new WeakSet();
const VIEWS = new WeakSet();
const COMPAT_PORTS = new WeakSet();
const COMPAT_VIEWS = new WeakMap();
const COMPAT_TARGETS = new WeakMap();
const COMPAT_DIRECTORIES = new WeakMap();
const DIGEST = (value) => `sha256:${createHash("sha256").update(canonicalJson(value)).digest("hex")}`;
const HASH = /^sha256:[0-9a-f]{64}$/;
const UID = /^W-[0-9A-HJKMNP-TV-Z]{26}$/;

function fail(message) { throw new Error(`sealed authority: ${message}`); }
function text(value, field) { if (typeof value !== "string" || !value) fail(`${field} is required`); return value.normalize("NFC"); }
function hash(value, field) { value = text(value, field); if (!HASH.test(value)) fail(`${field} is not a sha256 digest`); return value; }
function exactKeys(value, keys, label) {
  if (!value || typeof value !== "object" || Array.isArray(value)) fail(`${label} must be an object`);
  const actual = Object.keys(value).sort(); const expected = [...keys].sort();
  if (actual.length !== expected.length || actual.some((key, index) => key !== expected[index])) fail(`${label} has an invalid schema`);
}
function clone(value) { return JSON.parse(canonicalJson(value)); }
function atomicWrite(path, bytes) {
  mkdirSync(dirname(path), { recursive: true });
  const temporary = `${path}.tmp-${process.pid}-${Date.now()}`;
  let fd;
  try { fd = openSync(temporary, "wx", 0o600); writeFileSync(fd, bytes, "utf8"); fsyncSync(fd); }
  finally { if (fd !== undefined) closeSync(fd); }
  renameSync(temporary, path);
  fsyncDirectory(dirname(path));
}
function readCanonical(path) {
  const raw = readFileSync(path, "utf8"); const parsed = JSON.parse(raw);
  if (`${canonicalJson(parsed)}\n` !== raw) fail("non-canonical persisted authority bytes");
  return parsed;
}
function registryRevision(registry) { return registry.registryRevisionId(); }
function worktree(registry, worktreeUid) {
  if (!UID.test(worktreeUid)) fail("worktree UID is not opaque W-base32");
  const value = registry.worktree(worktreeUid); if (!value) fail("worktree is unavailable"); return value;
}
function validateRoot(root, registry, store) {
  exactKeys(root, ["projectUid", "baseSnapshotUid", "authoritySnapshotUid", "targetInventoryRoot"], "contributing root");
  for (const key of Object.keys(root)) text(root[key], key);
  hash(root.targetInventoryRoot, "targetInventoryRoot");
  const snapshot = store.openExactSnapshotV1(root.baseSnapshotUid);
  if (snapshot.project_uid !== root.projectUid) fail("root project does not match base snapshot");
  if (!registry.project(root.projectUid)) fail("root project is absent from registry");
  return freezeDeep(clone(root));
}
function validateInventory(inventory, manifest) {
  exactKeys(inventory, ["schema", "authoritySnapshotUid", "baseSnapshotUid", "registryRevisionId", "scope", "targets", "directories", "contributingProjectRoots"], "inventory");
  if (inventory.schema !== 1 || !Array.isArray(inventory.targets) || !Array.isArray(inventory.directories) || !Array.isArray(inventory.contributingProjectRoots)) fail("inventory schema is invalid");
  if (inventory.authoritySnapshotUid !== manifest.authoritySnapshotUid || inventory.baseSnapshotUid !== manifest.baseSnapshotUid || inventory.registryRevisionId !== manifest.registryRevisionId) fail("inventory binding mismatch");
  const targets = new Set();
  for (const target of inventory.targets) {
    exactKeys(target, ["targetUid", "kind", "contentDigest"], "target"); text(target.targetUid, "targetUid"); text(target.kind, "kind"); hash(target.contentDigest, "contentDigest");
    if (targets.has(target.targetUid)) fail("duplicate target"); targets.add(target.targetUid);
  }
  for (const directory of inventory.directories) {
    exactKeys(directory, ["targetUid", "orderingVersion", "maxPageLimit", "tokenBudget", "children"], "directory");
    if (!targets.has(directory.targetUid) || !Number.isSafeInteger(directory.maxPageLimit) || directory.maxPageLimit < 1 || directory.maxPageLimit > 100 || directory.tokenBudget !== 6000 || directory.orderingVersion !== "spipe-directory-order-v1") fail("directory bounds are invalid");
    if (!Array.isArray(directory.children) || new Set(directory.children).size !== directory.children.length || directory.children.some((child) => !targets.has(child))) fail("directory children are invalid");
  }
  if (DIGEST(inventory) !== manifest.targetInventoryRoot) fail("target inventory root mismatch");
}
function validateManifest(manifest) {
  exactKeys(manifest, ["schema", "workspaceUid", "projectUidOrNull", "worktreeUid", "baseSnapshotUid", "authoritySnapshotUid", "revisionId", "registryRevisionId", "targetInventoryRoot", "inventoryDigest", "contributingProjectRoots"], "authority manifest");
  if (manifest.schema !== 1 || !UID.test(manifest.worktreeUid)) fail("authority manifest schema is invalid");
  for (const field of ["workspaceUid", "worktreeUid", "baseSnapshotUid", "authoritySnapshotUid", "revisionId", "registryRevisionId", "targetInventoryRoot", "inventoryDigest"]) text(manifest[field], field);
  hash(manifest.targetInventoryRoot, "targetInventoryRoot"); hash(manifest.inventoryDigest, "inventoryDigest");
  if (!Array.isArray(manifest.contributingProjectRoots)) fail("aggregate roots missing");
}
function continuationDomain(manifest, directory) {
  return DIGEST({ authorityManifestDigest: DIGEST(manifest), targetUid: directory.targetUid, orderingVersion: directory.orderingVersion, maxPageLimit: directory.maxPageLimit, tokenBudget: directory.tokenBudget });
}

export function createSealedSnapshotAuthorityV1({ registry, snapshotStore, authorityRoot }) {
  if (!isWorkspaceRegistryV1(registry) || !isSnapshotStoreV1(snapshotStore)) throw new TypeError("official branded registry and snapshot store are required");
  const root = text(authorityRoot, "authorityRoot");
  const permit = Object.freeze({}); PERMITS.add(permit);
  const port = Object.freeze({
    mintCommitPublisherPermitV1() { return permit; },
    publishAuthorityInventoryV1({ permit: candidate, build }) {
      if (!PERMITS.has(candidate) || candidate !== permit) fail("publisher permit is not commit-issued");
      if (!build || typeof build !== "object") fail("publish build is required");
      const manifest = freezeDeep(clone(build.manifest)); const inventory = freezeDeep(clone(build.inventory));
      validateManifest(manifest); validateInventory(inventory, manifest);
      if (manifest.workspaceUid !== registry.workspace_uid || manifest.registryRevisionId !== registryRevision(registry)) fail("manifest is not current registry state");
      const currentWorktree = worktree(registry, manifest.worktreeUid);
      if (currentWorktree.project_uid !== manifest.projectUidOrNull && manifest.projectUidOrNull !== null) fail("worktree project mismatch");
      const snapshot = snapshotStore.openExactSnapshotV1(manifest.baseSnapshotUid);
      if (snapshot.worktree_uid !== manifest.worktreeUid || snapshot.revision_id !== manifest.revisionId) fail("base snapshot mismatch");
      if (manifest.inventoryDigest !== DIGEST(inventory)) fail("inventory digest mismatch");
      const roots = manifest.contributingProjectRoots.map((entry) => validateRoot(entry, registry, snapshotStore));
      const expected = roots.map(canonicalJson).sort(); if (canonicalJson(roots.map(canonicalJson).sort()) !== canonicalJson(expected)) fail("aggregate roots are not canonical");
      const name = `${manifest.authoritySnapshotUid}.json`; atomicWrite(join(root, name), `${canonicalJson({ manifest, inventory })}\n`);
      return freezeDeep({ authoritySnapshotUid: manifest.authoritySnapshotUid, authorityManifestDigest: DIGEST(manifest) });
    },
    openPublishedAuthorityInventoryV1(binding) {
      if (!binding || typeof binding !== "object") fail("binding required");
      const id = text(binding.authoritySnapshotUid, "authoritySnapshotUid");
      const published = readCanonical(join(root, `${id}.json`)); exactKeys(published, ["manifest", "inventory"], "published authority");
      const manifest = published.manifest; const inventory = published.inventory; validateManifest(manifest); validateInventory(inventory, manifest);
      if (manifest.authoritySnapshotUid !== id || binding.workspaceUid !== manifest.workspaceUid || binding.worktreeUid !== manifest.worktreeUid || binding.baseSnapshotUid !== manifest.baseSnapshotUid || binding.registryRevisionId !== manifest.registryRevisionId) fail("requested binding mismatch");
      const before = registryRevision(registry); if (before !== manifest.registryRevisionId) fail("registry revision changed");
      const wt = worktree(registry, manifest.worktreeUid); const snapshot = snapshotStore.openExactSnapshotV1(manifest.baseSnapshotUid);
      if (wt.project_uid !== snapshot.project_uid || snapshot.worktree_uid !== manifest.worktreeUid || snapshot.revision_id !== manifest.revisionId) fail("live registry snapshot mismatch");
      const after = registryRevision(registry); if (after !== before) fail("registry changed while opening authority");
      const view = Object.freeze({}); VIEWS.add(view);
      return view;
    },
    isSnapshotAuthorityViewV1(value) { return VIEWS.has(value); },
    deriveContinuationDomainV1(manifest, directory) {
      validateManifest(manifest);
      exactKeys(directory, ["targetUid", "orderingVersion", "maxPageLimit", "tokenBudget", "children"], "directory");
      if (!Number.isSafeInteger(directory.maxPageLimit) || directory.maxPageLimit < 1 || directory.maxPageLimit > 100 ||
          directory.tokenBudget !== 6000 || directory.orderingVersion !== "spipe-directory-order-v1" ||
          !Array.isArray(directory.children) || new Set(directory.children).size !== directory.children.length) fail("directory bounds are invalid");
      return continuationDomain(manifest, directory);
    }
  });
  PORTS.add(port); return port;
}
export function isSealedSnapshotAuthorityV1(value) { return PORTS.has(value); }

// Compatibility boundary for the original projection-port contract. The
// admitted sealed service above remains unchanged; this adapter only consumes
// the branded in-memory TargetInventoryStore used by the legacy port tests.
export function createSnapshotAuthorityPortV1({ workspaceRegistry, snapshotStore, targetInventoryStore, authorityInstanceUid = "authority-instance-v1" } = {}) {
  if (!workspaceRegistry || !snapshotStore || !targetInventoryStore || typeof targetInventoryStore.get !== "function") throw new TypeError("SnapshotAuthorityPortV1 requires trusted stores");
  const ok = (value) => Object.freeze({ ok: true, value });
  const denied = () => Object.freeze({ ok: false, error: { code: "authority_denied" } });
  const port = Object.freeze({
    openBoundSnapshot(binding) {
      try {
        const fields = ["workspaceUid", "projectUidOrNull", "worktreeUid", "snapshotUid", "revisionId"];
        if (!binding || Object.keys(binding).sort().join("\0") !== fields.slice().sort().join("\0") || binding.workspaceUid !== workspaceRegistry.workspace_uid) return denied();
        const record = targetInventoryStore.get(binding.snapshotUid); const authority = record?.authority; const inventory = record?.inventory;
        if (!authority || !inventory || authority.snapshot_uid !== binding.snapshotUid || authority.workspace_uid !== binding.workspaceUid || authority.project_uid !== binding.projectUidOrNull || authority.worktree_uid !== binding.worktreeUid || authority.revision_id !== binding.revisionId) return denied();
        const liveWorktree = workspaceRegistry.worktree(binding.worktreeUid);
        if (!liveWorktree || liveWorktree.revision_id !== binding.revisionId || `sha256:${createHash("sha256").update(canonicalJson({ ...inventory, root_digest: undefined })).digest("hex")}` !== inventory.root_digest) return denied();
        const base = snapshotStore.read(authority.base_snapshot_uid);
        if (!base || base.worktree_uid !== binding.worktreeUid || base.revision_id !== binding.revisionId || (binding.projectUidOrNull !== null && base.project_uid !== binding.projectUidOrNull)) return denied();
        const state = { port, binding, authority, inventory, authorityInstanceUid, manifestDigest: authority.snapshot_uid };
        const view = Object.freeze({ authority_instance: authorityInstanceUid, snapshot_uid: binding.snapshotUid, inventory_root: inventory.root_digest, manifest_digest: authority.snapshot_uid });
        COMPAT_VIEWS.set(view, state); return ok(view);
      } catch { return denied(); }
    },
    resolveCanonicalTarget(view, request) {
      const state = COMPAT_VIEWS.get(view); if (!state || !request || Object.keys(request).sort().join("\0") !== "targetKind\0targetUid") return denied();
      const entry = state.inventory.entries.find((item) => item.target_kind === request.targetKind && item.target_uid === request.targetUid); if (!entry) return denied();
      const target = Object.freeze({ authority_instance: state.authorityInstanceUid, snapshot_uid: state.binding.snapshotUid, inventory_root: state.inventory.root_digest, manifest_digest: state.manifestDigest, target_kind: entry.target_kind, target_uid: entry.target_uid, content_digest: entry.content_digest, children: entry.children ?? [] });
      COMPAT_TARGETS.set(target, state); return ok(target);
    },
    resolveCanonicalAlias(view, request) {
      const state = COMPAT_VIEWS.get(view); if (!state || !request) return denied();
      const alias = state.inventory.alias_index.find((item) => item.normalized_alias_uri === request.normalizedAliasUri); return alias ? ok(Object.freeze({ ...alias })) : denied();
    },
    listDirectoryTarget(view, request) {
      const state = COMPAT_VIEWS.get(view); if (!state || !request) return denied();
      const entry = state.inventory.entries.find((item) => item.target_kind === "directory" && item.view_kind === request.viewKind && item.logical_path === request.normalizedLogicalPath && item.selector_digest === request.selectorDigest); if (!entry) return denied();
      const directory = Object.freeze({ authority_instance: state.authorityInstanceUid, snapshot_uid: state.binding.snapshotUid, inventory_root: state.inventory.root_digest, manifest_digest: state.manifestDigest, target_kind: entry.target_kind, target_uid: entry.target_uid, selector_digest: entry.selector_digest, children: entry.children ?? [] });
      COMPAT_DIRECTORIES.set(directory, state); return ok(directory);
    }
  });
  COMPAT_PORTS.add(port); return port;
}

export function isSnapshotAuthorityPortV1(value) { return PORTS.has(value) || COMPAT_PORTS.has(value); }
export function isSnapshotAuthorityViewV1(value) { return VIEWS.has(value) || COMPAT_VIEWS.has(value); }
export function isViewForSnapshotAuthorityPortV1(port, view) { return COMPAT_VIEWS.get(view)?.port === port; }
export function isCanonicalTargetV1(value) { return COMPAT_TARGETS.has(value); }
export function isCanonicalDirectoryTargetV1(value) { return COMPAT_DIRECTORIES.has(value); }
