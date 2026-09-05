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

const PORTS = new WeakSet();
const PERMITS = new WeakSet();
const VIEWS = new WeakSet();
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
  const parent = openSync(dirname(path), "r"); try { fsyncSync(parent); } finally { closeSync(parent); }
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
