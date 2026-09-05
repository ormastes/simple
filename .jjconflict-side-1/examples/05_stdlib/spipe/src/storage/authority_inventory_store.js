import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { canonicalJson, freezeDeep } from "./canonical.js";
import { canonicalRoot, safeNamespace } from "../workspace/paths.js";

const STORES = new WeakSet();
const SHA256 = /^[0-9a-f]{64}$/;
const WORKTREE = /^W-[0-9A-HJKMNP-TV-Z]{26}$/;
const UID = /^[A-Z][A-Z0-9]*-[A-Za-z0-9_-]{1,190}$/;

function sha(value) { return createHash("sha256").update(canonicalJson(value)).digest("hex"); }
function text(value, name) {
  if (typeof value !== "string" || value.length === 0) throw new TypeError(`${name} is required`);
  return value.normalize("NFC");
}
function digest(value, name) {
  const result = text(value, name).replace(/^sha256:/, "");
  if (!SHA256.test(result)) throw new TypeError(`${name} must be sha256`);
  return result;
}
function worktree(value) {
  const result = text(value, "worktreeUid");
  if (!WORKTREE.test(result)) throw new TypeError("worktreeUid must be W-<opaque-base32>");
  return result;
}
function uid(value, name) { const result = text(value, name); if (!UID.test(result)) throw new TypeError(`${name} is invalid`); return result; }
function canonicalContributors(scopeKind, value) {
  if (scopeKind === "project") {
    if (value !== undefined && value !== null && (!Array.isArray(value) || value.length)) throw new TypeError("project inventory forbids contributors");
    return [];
  }
  if (!Array.isArray(value)) throw new TypeError("aggregate inventory requires contributors");
  const rows = value.map((row) => ({
    projectUid: uid(row?.projectUid, "contributor projectUid"),
    baseSnapshotUid: text(row?.baseSnapshotUid, "contributor baseSnapshotUid"),
    authoritySnapshotUid: text(row?.authoritySnapshotUid, "contributor authoritySnapshotUid"),
    targetInventoryRoot: digest(row?.targetInventoryRoot, "contributor targetInventoryRoot")
  }));
  const sorted = [...rows].sort((a, b) => a.projectUid.localeCompare(b.projectUid));
  if (canonicalJson(rows) !== canonicalJson(sorted) || new Set(rows.map((row) => row.projectUid)).size !== rows.length) throw new TypeError("contributors must be unique and canonical project order");
  return rows;
}
function canonicalEntries(entries) {
  if (!Array.isArray(entries)) throw new TypeError("inventory entries must be an array");
  const rows = entries.map((entry) => ({
    targetKind: text(entry?.targetKind, "entry targetKind"), targetUid: uid(entry?.targetUid, "entry targetUid"),
    contentDigest: digest(entry?.contentDigest, "entry contentDigest"), locator: text(entry?.locator ?? entry?.targetUid, "entry locator"),
    children: entry.children === undefined ? [] : entry.children.map((child) => uid(child, "directory child"))
  }));
  const sorted = [...rows].sort((a, b) => `${a.targetKind}\0${a.targetUid}`.localeCompare(`${b.targetKind}\0${b.targetUid}`));
  if (canonicalJson(rows) !== canonicalJson(sorted) || new Set(rows.map((row) => `${row.targetKind}\0${row.targetUid}`)).size !== rows.length) throw new TypeError("inventory entries must be unique and canonical");
  return rows;
}
function canonicalAliases(value, entries) {
  if (value == null) return [];
  if (!Array.isArray(value)) throw new TypeError("aliasIndex must be an array");
  const valid = new Set(entries.map((entry) => `${entry.targetKind}\0${entry.targetUid}`));
  const rows = value.map((entry) => ({ alias: text(entry?.alias, "alias"), targetKind: text(entry?.targetKind, "alias targetKind"), targetUid: uid(entry?.targetUid, "alias targetUid") }));
  for (const row of rows) if (!valid.has(`${row.targetKind}\0${row.targetUid}`)) throw new TypeError("alias target is not in inventory");
  const sorted = [...rows].sort((a, b) => a.alias.localeCompare(b.alias));
  if (canonicalJson(rows) !== canonicalJson(sorted) || new Set(rows.map((row) => row.alias)).size !== rows.length) throw new TypeError("aliases must be unique and canonical");
  return rows;
}
function inventoryUnsigned(input) {
  const scopeKind = input.scopeKind;
  if (!["project", "workspace_aggregate"].includes(scopeKind)) throw new TypeError("inventory scopeKind is invalid");
  const projectUidOrNull = input.projectUidOrNull ?? null;
  if ((scopeKind === "project") !== (projectUidOrNull !== null)) throw new TypeError("inventory project scope mismatch");
  const entries = canonicalEntries(input.entries);
  return {
    version: 1, scopeKind, workspaceUid: uid(input.workspaceUid, "workspaceUid"), projectUidOrNull: projectUidOrNull === null ? null : uid(projectUidOrNull, "projectUid"),
    worktreeUid: worktree(input.worktreeUid), baseSnapshotUid: text(input.baseSnapshotUid, "baseSnapshotUid"), revisionId: text(input.revisionId, "revisionId"),
    entries, aliasIndex: canonicalAliases(input.aliasIndex, entries), projectionRoot: digest(input.projectionRoot ?? sha256(entries), "projectionRoot"),
    contributingProjectRoots: canonicalContributors(scopeKind, input.contributingProjectRoots)
  };
}
export function createTargetInventoryManifestV1(input) {
  const unsigned = inventoryUnsigned(input);
  const rootDigest = sha(unsigned);
  if (input.rootDigest !== undefined && digest(input.rootDigest, "rootDigest") !== rootDigest) throw new Error("inventory root digest mismatch");
  return freezeDeep({ ...unsigned, rootDigest });
}
export function createAuthorityManifestV1(input) {
  const inventory = createTargetInventoryManifestV1(input.inventory);
  const unsigned = {
    version: 1, workspaceUid: inventory.workspaceUid, projectUidOrNull: inventory.projectUidOrNull,
    worktreeUid: inventory.worktreeUid, baseSnapshotUid: inventory.baseSnapshotUid, revisionId: inventory.revisionId,
    scopeKind: inventory.scopeKind, targetInventoryRoot: inventory.rootDigest, contributingProjectRoots: inventory.contributingProjectRoots
  };
  const snapshotUid = `spka1-${sha(unsigned)}`;
  if (input.snapshotUid !== undefined && input.snapshotUid !== snapshotUid) throw new Error("authority snapshot UID mismatch");
  return freezeDeep({ ...unsigned, snapshotUid });
}
function atomic(path, value) {
  mkdirSync(dirname(path), { recursive: true });
  const temp = `${path}.tmp-${process.pid}-${Date.now()}`;
  writeFileSync(temp, `${canonicalJson(value)}\n`, { encoding: "utf8", flag: "wx" });
  renameSync(temp, path);
}
/** Content-addressed authority manifests. Only KnowledgeCompiler publishes through this store. */
export class TargetInventoryStoreV1 {
  constructor({ cacheRoot, repositoryId = "default" } = {}) {
    this.root = join(canonicalRoot(cacheRoot), "shared", safeNamespace(repositoryId, "repository id"), "authority-inventories");
    mkdirSync(this.root, { recursive: true }); STORES.add(this);
  }
  publishAuthorityInventoryV1(build) {
    if (!build || build.publisher !== "KnowledgeCompiler") throw new TypeError("only KnowledgeCompiler may publish authority inventories");
    const inventory = createTargetInventoryManifestV1(build.inventory);
    const authority = createAuthorityManifestV1({ inventory });
    const path = join(this.root, `${authority.snapshotUid}.sdn`);
    const record = { inventory, authority };
    if (existsSync(path)) {
      if (readFileSync(path, "utf8") !== `${canonicalJson(record)}\n`) throw new Error("authority inventory collision");
    } else atomic(path, record);
    return freezeDeep(record);
  }
  openPublishedAuthorityInventoryV1(binding) {
    const snapshotUid = text(binding?.authoritySnapshotUid, "authority snapshotUid");
    const path = join(this.root, `${snapshotUid}.sdn`);
    if (!existsSync(path)) return null;
    const record = JSON.parse(readFileSync(path, "utf8"));
    const inventory = createTargetInventoryManifestV1(record.inventory);
    const authority = createAuthorityManifestV1({ inventory, snapshotUid: record.authority?.snapshotUid });
    if (canonicalJson({ inventory, authority }) !== canonicalJson(record)) throw new Error("authority inventory failed verification");
    for (const field of ["workspaceUid", "projectUidOrNull", "worktreeUid", "baseSnapshotUid", "revisionId"]) {
      if (binding[field] !== authority[field]) return null;
    }
    return freezeDeep({ inventory, authority });
  }
}
export function createTargetInventoryStoreV1(options) { return new TargetInventoryStoreV1(options); }
export function isTargetInventoryStoreV1(value) { return Boolean(value && STORES.has(value)); }
