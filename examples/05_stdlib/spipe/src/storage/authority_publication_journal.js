import { randomBytes } from "node:crypto";
import { closeSync, existsSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, unlinkSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

import { canonicalJson, contentHash, freezeDeep, sha256Hex } from "./canonical.js";
import { canonicalRoot, safeNamespace } from "../workspace/paths.js";

const JOURNAL_BRAND = new WeakSet();
const JOURNAL_STATE = new WeakMap();

function required(value, name) {
  if (typeof value !== "string" || value.length === 0) throw new TypeError(`${name} must be a non-empty string`);
  return value.normalize("NFC");
}
function digest(value, name) {
  const text = required(value, name);
  if (!/^sha256:[0-9a-f]{64}$/.test(text)) throw new TypeError(`${name} must be sha256-prefixed`);
  return text;
}
function syncDirectory(path) { let fd; try { fd = openSync(path, "r"); fsyncSync(fd); } finally { if (fd !== undefined) closeSync(fd); } }
function writeDurable(path, bytes, checkpoint = () => {}) {
  mkdirSync(dirname(path), { recursive: true });
  const temporary = `${path}.tmp-${process.pid}-${randomBytes(12).toString("hex")}`;
  checkpoint("stage");
  let fd;
  try { fd = openSync(temporary, "wx"); checkpoint("write"); writeFileSync(fd, bytes); fsyncSync(fd); checkpoint("file-fsync"); }
  finally { if (fd !== undefined) closeSync(fd); }
  checkpoint("rename"); renameSync(temporary, path); checkpoint("parent-fsync"); syncDirectory(dirname(path));
}
function canonicalRecord(value) {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new TypeError("AuthorityPublicationRecordV1 must be an object");
  const fields = ["authority_manifest_digest", "authority_snapshot_uid", "base_snapshot_uid", "commit_id", "inventory_manifest_digest", "publication_uid", "registry_revision_id", "revision_id", "schema", "worktree_uid"];
  if (Object.keys(value).sort().join("\0") !== fields.join("\0")) throw new TypeError("AuthorityPublicationRecordV1 has a closed schema");
  const record = {
    schema: "spipe-authority-publication-v1",
    publication_uid: required(value.publication_uid, "publication_uid"), commit_id: required(value.commit_id, "commit_id"),
    worktree_uid: required(value.worktree_uid, "worktree_uid"), revision_id: required(value.revision_id, "revision_id"),
    registry_revision_id: digest(value.registry_revision_id, "registry_revision_id"), base_snapshot_uid: required(value.base_snapshot_uid, "base_snapshot_uid"),
    authority_snapshot_uid: required(value.authority_snapshot_uid, "authority_snapshot_uid"),
    authority_manifest_digest: digest(value.authority_manifest_digest, "authority_manifest_digest"),
    inventory_manifest_digest: digest(value.inventory_manifest_digest, "inventory_manifest_digest")
  };
  if (value.schema !== record.schema) throw new TypeError("AuthorityPublicationRecordV1 schema is invalid");
  return freezeDeep(record);
}
function recordUid(record) { return `app1-${sha256Hex(canonicalJson(record))}`; }

/** Sole durable owner of authority-publication staging, recovery, and current-pointer CAS. */
export class AuthorityPublicationJournalV1 {
  constructor({ cacheRoot, repositoryId = "default", worktreeUid, faultInjector = null }) {
    this.cache_root = canonicalRoot(String(cacheRoot ?? ""));
    if (!cacheRoot) throw new TypeError("cacheRoot is required");
    this.repository_id = safeNamespace(String(repositoryId), "repository id"); this.worktree_uid = required(worktreeUid, "worktreeUid");
    if (faultInjector !== null && typeof faultInjector !== "function") throw new TypeError("faultInjector must be a function or null");
    this.fault_injector = faultInjector;
    this.root = join(this.cache_root, "worktrees", this.worktree_uid, "authority-publications");
    this.records_root = join(this.root, "records"); this.objects_root = join(this.root, "objects"); this.current_path = join(this.root, "current.sdn"); this.lock_path = join(this.root, "writer.lock");
    mkdirSync(this.records_root, { recursive: true }); mkdirSync(this.objects_root, { recursive: true }); syncDirectory(this.records_root); syncDirectory(this.objects_root);
    JOURNAL_BRAND.add(this); JOURNAL_STATE.set(this, { id: randomBytes(16).toString("hex") });
  }
  current() {
    if (!existsSync(this.current_path)) return null;
    const record = canonicalRecord(JSON.parse(readFileSync(this.current_path, "utf8")));
    const file = join(this.records_root, `${safeNamespace(record.publication_uid, "publication uid")}.sdn`);
    if (!existsSync(file) || !readFileSync(file).equals(Buffer.from(`${canonicalJson(record)}\n`))) throw new Error("SPK803 current authority publication is incomplete");
    const authority = JSON.parse(this.readImmutableObjectV1(record.authority_manifest_digest).toString("utf8"));
    const inventory = JSON.parse(this.readImmutableObjectV1(record.inventory_manifest_digest).toString("utf8"));
    if (!authority || authority.schema !== "spipe-authority-manifest-v1" || authority.base_snapshot_uid !== record.base_snapshot_uid ||
        authority.authority_snapshot_uid !== record.authority_snapshot_uid || authority.registry_revision_id !== record.registry_revision_id ||
        authority.inventory_manifest_digest !== record.inventory_manifest_digest || !inventory || inventory.schema !== "spipe-target-inventory-v1" ||
        inventory.base_snapshot_uid !== record.base_snapshot_uid || inventory.registry_revision_id !== record.registry_revision_id) {
      throw new Error("SPK803 published authority manifests do not bind the current record");
    }
    return record;
  }
  /** Persist one sealed content-addressed object before a publication can name it. */
  putImmutableObjectV1(bytes, expectedDigest = null) {
    const value = Buffer.isBuffer(bytes) ? bytes : Buffer.from(bytes);
    const actual = contentHash(value);
    if (expectedDigest !== null && digest(expectedDigest, "expectedDigest") !== actual) throw new Error("SPK803 immutable authority object digest mismatch");
    const path = join(this.objects_root, actual.slice(7));
    if (existsSync(path)) { if (!readFileSync(path).equals(value)) throw new Error("SPK803 immutable authority object collision"); }
    else writeDurable(path, value, (boundary) => this.#checkpoint(`object-${boundary}`));
    return actual;
  }
  readImmutableObjectV1(expectedDigest) {
    const value = digest(expectedDigest, "expectedDigest"), path = join(this.objects_root, value.slice(7));
    if (!existsSync(path)) throw new Error("SPK803 published authority object is missing");
    const bytes = readFileSync(path); if (contentHash(bytes) !== value) throw new Error("SPK803 published authority object digest mismatch");
    return bytes;
  }
  publishAuthorityPublicationV1(expectedPublicationUid, input) {
    const record = canonicalRecord(input);
    if (record.worktree_uid !== this.worktree_uid) throw new TypeError("publication worktree mismatch");
    if (record.publication_uid !== recordUid({ ...record, publication_uid: "pending" })) {
      // A caller may use a semantic UID, but it may never collide with different immutable bytes.
      required(record.publication_uid, "publication_uid");
    }
    const lock = this.#lock();
    try {
      const current = this.current();
      if ((current?.publication_uid ?? null) !== (expectedPublicationUid ?? null)) throw new Error("SPK901 authority publication compare-and-swap conflict");
      const bytes = Buffer.from(`${canonicalJson(record)}\n`, "utf8");
      const path = join(this.records_root, `${safeNamespace(record.publication_uid, "publication uid")}.sdn`);
      if (existsSync(path)) { if (!readFileSync(path).equals(bytes)) throw new Error("SPK803 immutable authority publication collision"); }
      else writeDurable(path, bytes, (boundary) => this.#checkpoint(`publication-record-${boundary}`));
      // All content named by the closed record must have crossed its own file
      // and parent-directory durability boundary before this visibility CAS.
      // `current()` repeats full object and cross-manifest validation after the
      // pointer is durable; preflight here prevents a pointer to absent bytes.
      this.readImmutableObjectV1(record.authority_manifest_digest); this.readImmutableObjectV1(record.inventory_manifest_digest);
      // The current pointer is the only visibility boundary; it is atomically replaced after record durability.
      this.#checkpoint("current-pointer-cas");
      writeDurable(this.current_path, bytes, (boundary) => this.#checkpoint(`current-pointer-${boundary}`));
      this.#checkpoint("ack");
      return freezeDeep({ status: "published", previous_publication_uid: current?.publication_uid ?? null, record });
    } finally { closeSync(lock); unlinkSync(this.lock_path); syncDirectory(dirname(this.lock_path)); }
  }
  recoverAuthorityPublicationV1() { return freezeDeep({ status: "recovered", record: this.current() }); }
  #lock() {
    mkdirSync(dirname(this.lock_path), { recursive: true });
    try { return openSync(this.lock_path, "wx"); } catch { throw new Error("SPK901 authority publication writer is busy"); }
  }
  #checkpoint(boundary) { if (this.fault_injector !== null) this.fault_injector(boundary); }
}
export function isAuthorityPublicationJournalV1(value) { return JOURNAL_BRAND.has(value) && JOURNAL_STATE.has(value); }
export { canonicalRecord as validateAuthorityPublicationRecordV1 };
