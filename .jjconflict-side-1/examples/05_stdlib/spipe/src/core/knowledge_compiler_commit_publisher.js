import { randomBytes } from "node:crypto";
import {
  closeSync, existsSync, fsyncSync, linkSync, lstatSync, mkdirSync, openSync,
  readFileSync, renameSync, statSync, unlinkSync, writeFileSync
} from "node:fs";
import { dirname, join } from "node:path";

import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";
import { isImmutableSnapshotStoreV1 } from "../storage/snapshot_store.js";
import { isWorkspaceRegistryV1 } from "../workspace/registry.js";

const STORE_STATE = new WeakMap();
const PERMIT_STATE = new WeakMap();
const ISSUER_STATE = new WeakMap();
const STORE_CONSTRUCTOR_TOKEN = Symbol("TargetInventoryStoreV1.constructor");
const ISSUER_CONSTRUCTOR_TOKEN = Symbol("PublisherPermitIssuerV1.constructor");
const AUTHORITY_INPUT_FIELDS = Object.freeze([
  "commitId", "workspaceUid", "projectUidOrNull", "worktreeUid", "revisionId",
  "expectedRegistryRevisionId", "expectedBaseSnapshotUidOrNull",
  "expectedPublicationUidOrNull", "inputDeltas"
]);
const REPLAY_SCHEMA_VERSION = 1;
const REPLAY_RESULT_FIELDS = Object.freeze(["canonical_input", "replay_envelope_digest"]);

function fsyncDirectory(path) {
  const descriptor = openSync(path, "r");
  try { fsyncSync(descriptor); } finally { closeSync(descriptor); }
}

/**
 * Create one path component at a time. EEXIST is an expected concurrent
 * first-use outcome, but only after the winner's directory has been checked
 * and durably observed. Both the parent entry and the new/observed directory
 * are synced, so every ledger ancestor is on the durability chain.
 */
function mkdirDurable(path) {
  const missing = [];
  let current = path;
  for (;;) {
    try {
      const observed = lstatSync(current);
      if (!observed.isDirectory() || observed.isSymbolicLink()) throw new Error("replay ledger ancestor is not a real directory");
      break;
    } catch (error) {
      if (error?.code !== "ENOENT") throw error;
      missing.push(current);
      const parent = dirname(current);
      if (parent === current) throw new Error("replay ledger has no existing ancestor");
      current = parent;
    }
  }
  for (const directory of missing.reverse()) {
    try {
      mkdirSync(directory);
    } catch (error) {
      if (error?.code !== "EEXIST") throw error;
    }
    const observed = lstatSync(directory);
    if (!observed.isDirectory() || observed.isSymbolicLink()) throw new Error("replay ledger ancestor is not a real directory");
    fsyncDirectory(dirname(directory));
    fsyncDirectory(directory);
  }
  // A losing first-use process can observe a directory created by its winner.
  // It must make that observation durable before it acknowledges initialization.
  const observed = lstatSync(path);
  if (!observed.isDirectory() || observed.isSymbolicLink()) throw new Error("replay ledger ancestor is not a real directory");
  fsyncDirectory(dirname(path));
  fsyncDirectory(path);
}

function atomicCanonicalWrite(path, value) {
  mkdirDurable(dirname(path));
  const temporary = `${path}.tmp-${process.pid}-${randomBytes(12).toString("hex")}`;
  const descriptor = openSync(temporary, "wx", 0o600);
  try {
    writeFileSync(descriptor, canonicalJson(value), { encoding: "utf8" });
    fsyncSync(descriptor);
  } finally { closeSync(descriptor); }
  renameSync(temporary, path);
  fsyncDirectory(dirname(path));
}

function closedCanonicalObject(value, fields, label) {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new Error(`${label} is not an object`);
  const keys = Object.keys(value);
  if (keys.length !== fields.length || keys.some((key) => !fields.includes(key))) throw new Error(`${label} has an invalid schema`);
  if (canonicalJson(value) !== canonicalJson(Object.fromEntries(fields.map((key) => [key, value[key]])))) {
    throw new Error(`${label} is not canonical`);
  }
  return value;
}

function processIsAlive(pid) {
  if (!Number.isSafeInteger(pid) || pid <= 0) return false;
  try { process.kill(pid, 0); return true; }
  catch (error) { return error?.code === "EPERM"; }
}

function text(value, name) {
  if (typeof value !== "string" || value.length === 0) throw new TypeError(`${name} must be a non-empty string`);
  return value.normalize("NFC");
}

function nullableText(value, name) { return value === null ? null : text(value, name); }

function closedObject(value, fields, name) {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new TypeError(`${name} must be an object`);
  const keys = Reflect.ownKeys(value);
  if (keys.some((key) => typeof key !== "string" || !Object.prototype.propertyIsEnumerable.call(value, key))) {
    throw new TypeError(`${name} cannot contain symbols or non-enumerable fields`);
  }
  if (keys.sort().join("\0") !== [...fields].sort().join("\0")) {
    throw new TypeError(`${name} fields must match the closed schema exactly`);
  }
  const snapshot = Object.create(null);
  for (const key of fields) {
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (!descriptor || !Object.hasOwn(descriptor, "value") || descriptor.get !== undefined || descriptor.set !== undefined) {
      throw new TypeError(`${name} fields must be enumerable data properties`);
    }
    Object.defineProperty(snapshot, key, { value: descriptor.value, enumerable: true });
  }
  return snapshot;
}

/** Snapshots accepted delta data once and NFC-normalizes every string value. */
function canonicalValue(value) {
  if (value === null || typeof value === "boolean") return value;
  if (typeof value === "string") return value.normalize("NFC");
  if (typeof value === "number") {
    if (!Number.isFinite(value) || Object.is(value, -0)) throw new TypeError("inputDeltas numbers must be finite canonical values");
    return value;
  }
  if (Array.isArray(value)) {
    const keys = Reflect.ownKeys(value);
    const expected = Array.from({ length: value.length }, (_, index) => String(index));
    if (keys.length !== expected.length + 1 || keys.at(-1) !== "length" || keys.slice(0, -1).join("\0") !== expected.join("\0")) {
      throw new TypeError("inputDeltas arrays must be dense and cannot have extra properties");
    }
    return expected.map((key) => {
      const descriptor = Object.getOwnPropertyDescriptor(value, key);
      if (!descriptor || !Object.hasOwn(descriptor, "value") || descriptor.get !== undefined || descriptor.set !== undefined) {
        throw new TypeError("inputDeltas arrays must contain data values only");
      }
      return canonicalValue(descriptor.value);
    });
  }
  if (!value || typeof value !== "object" || Object.getPrototypeOf(value) !== Object.prototype) {
    throw new TypeError("inputDeltas values must be plain JSON values");
  }
  if (Reflect.ownKeys(value).some((key) => typeof key !== "string" || !Object.prototype.propertyIsEnumerable.call(value, key))) {
    throw new TypeError("inputDeltas values cannot contain symbols or non-enumerable fields");
  }
  const result = Object.create(null);
  const normalizedKeys = new Set();
  for (const key of Object.keys(value).sort()) {
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (!descriptor || !Object.hasOwn(descriptor, "value") || descriptor.get !== undefined || descriptor.set !== undefined) {
      throw new TypeError("inputDeltas values must contain data properties only");
    }
    const normalizedKey = key.normalize("NFC");
    if (normalizedKeys.has(normalizedKey)) throw new TypeError("inputDeltas keys must be unique after NFC normalization");
    normalizedKeys.add(normalizedKey);
    if (descriptor.value === undefined || typeof descriptor.value === "bigint") throw new TypeError("inputDeltas cannot contain undefined or bigint values");
    Object.defineProperty(result, normalizedKey, { value: canonicalValue(descriptor.value), enumerable: true });
  }
  return result;
}

/** Closed root-free selection input for the later P2 publisher transaction. */
export function selectCanonicalAuthorityInputV1(input) {
  const raw = closedObject(input, AUTHORITY_INPUT_FIELDS, "CommitInputV1");
  if (!Array.isArray(raw.inputDeltas)) throw new TypeError("CommitInputV1.inputDeltas must be an array");
  const selected = {
    schema_version: 1,
    commit_id: text(raw.commitId, "CommitInputV1.commitId"),
    workspace_uid: text(raw.workspaceUid, "CommitInputV1.workspaceUid"),
    project_uid_or_null: nullableText(raw.projectUidOrNull, "CommitInputV1.projectUidOrNull"),
    worktree_uid: text(raw.worktreeUid, "CommitInputV1.worktreeUid"),
    revision_id: text(raw.revisionId, "CommitInputV1.revisionId"),
    expected_registry_revision_id: text(raw.expectedRegistryRevisionId, "CommitInputV1.expectedRegistryRevisionId"),
    expected_base_snapshot_uid_or_null: nullableText(raw.expectedBaseSnapshotUidOrNull, "CommitInputV1.expectedBaseSnapshotUidOrNull"),
    expected_publication_uid_or_null: nullableText(raw.expectedPublicationUidOrNull, "CommitInputV1.expectedPublicationUidOrNull"),
    input_deltas: canonicalValue(raw.inputDeltas)
  };
  if ((selected.expected_base_snapshot_uid_or_null === null) !== (selected.expected_publication_uid_or_null === null)) {
    throw new TypeError("initial publication requires both expected IDs to be null; subsequent publication requires both");
  }
  return freezeDeep(selected);
}

export function canonicalAuthorityInputDigestV1(inputOrSelected) {
  const selected = inputOrSelected?.schema_version === 1 && Object.hasOwn(inputOrSelected, "commit_id")
    ? inputOrSelected
    : selectCanonicalAuthorityInputV1(inputOrSelected);
  return `sha256:${sha256Hex(canonicalJson(selected))}`;
}

/** Commit scope excludes mutable bindings: a changed binding conflicts. */
function replayScopeV1(selected) {
  return Object.freeze({ schema_version: REPLAY_SCHEMA_VERSION, commit_id: selected.commit_id });
}

function replayScopeDigestV1(selected) {
  return `sha256:${sha256Hex(canonicalJson(replayScopeV1(selected)))}`;
}

function replayResultV1(selected, envelopeDigest) {
  return freezeDeep({ canonical_input: selected, replay_envelope_digest: envelopeDigest });
}

/**
 * Durable commit-scoped idempotency ledger. It owns only replay records and
 * lock recovery; it is not the later publication journal/CAS implementation.
 */
class ReplayLedgerV1 {
  constructor(cacheRoot) {
    this.sharedRoot = join(cacheRoot, "shared");
    this.spipeRoot = join(this.sharedRoot, "spipe");
    this.root = join(this.spipeRoot, "commit-replay-v1");
    this.recordsRoot = join(this.root, "records");
    this.locksRoot = join(this.root, "locks");
    // Validate and durably observe each untrusted ledger component separately:
    // a symlink at shared/spipe/root is never accepted merely because a deeper
    // resolved target happens to be a real directory.
    mkdirDurable(this.sharedRoot);
    mkdirDurable(this.spipeRoot);
    mkdirDurable(this.root);
    mkdirDurable(this.recordsRoot);
    mkdirDurable(this.locksRoot);
  }

  _scopeName(selected) { return replayScopeDigestV1(selected).slice("sha256:".length); }
  _recordPath(selected) { return join(this.recordsRoot, `${this._scopeName(selected)}.json`); }
  _lockPath(selected) { return join(this.locksRoot, `${this._scopeName(selected)}.lock`); }
  _reclaimPath(selected) { return join(this.locksRoot, `.${this._scopeName(selected)}.reclaim`); }

  _readLock(path) {
    try {
      const raw = readFileSync(path, "utf8");
      const value = JSON.parse(raw);
      if (canonicalJson(value) !== raw || !value || value.schema_version !== REPLAY_SCHEMA_VERSION || !Number.isSafeInteger(value.pid)) return null;
      return Object.freeze({ value, digest: `sha256:${sha256Hex(raw)}` });
    } catch { return null; }
  }

  _acquire(selected) {
    const path = this._lockPath(selected);
    for (let attempt = 0; attempt < 1_000; attempt += 1) {
      const staging = join(this.locksRoot, `.${this._scopeName(selected)}.${process.pid}.${randomBytes(12).toString("hex")}.owner`);
      try {
        // Persist the owner receipt before one hard link makes ownership visible.
        const descriptor = openSync(staging, "wx", 0o600);
        try {
          writeFileSync(descriptor, canonicalJson(Object.freeze({ schema_version: REPLAY_SCHEMA_VERSION, pid: process.pid })), { encoding: "utf8" });
          fsyncSync(descriptor);
        } finally { closeSync(descriptor); }
        linkSync(staging, path);
        unlinkSync(staging);
        fsyncDirectory(this.locksRoot);
        return path;
      } catch (error) {
        try { unlinkSync(staging); } catch (cleanup) { if (cleanup?.code !== "ENOENT") throw cleanup; }
        if (error?.code !== "EEXIST") throw error;
        const owner = this._readLock(path);
        if (!owner) throw new Error("replay ledger lock owner receipt is corrupt");
        if (!processIsAlive(owner.value.pid)) {
          const claim = this._reclaimPath(selected);
          try {
            // The fixed claim serializes reclaimers. It is a hard link to the
            // exact stale inode, so a live replacement cannot be removed after
            // the revalidation below. A creator crash can leave the staging
            // receipt linked too; link count is deliberately not an authority.
            linkSync(path, claim);
            const claimOwner = this._readLock(claim);
            const observed = statSync(claim);
            const current = statSync(path);
            if (claimOwner?.digest === owner.digest && current.dev === observed.dev && current.ino === observed.ino && !processIsAlive(claimOwner.value.pid)) {
              unlinkSync(path);
              fsyncDirectory(this.locksRoot);
              continue;
            }
          } catch (claimError) {
            if (claimError?.code !== "ENOENT" && claimError?.code !== "EEXIST") throw claimError;
          } finally {
            try { unlinkSync(claim); } catch (cleanup) { if (cleanup?.code !== "ENOENT") throw cleanup; }
          }
        }
        Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 5);
      }
    }
    throw new Error("replay ledger lock timed out while live writer held scope");
  }

  _release(path) {
    const owner = this._readLock(path);
    if (!owner || owner.value.pid !== process.pid) throw new Error("replay ledger lock ownership changed before release");
    unlinkSync(path);
    fsyncDirectory(this.locksRoot);
  }

  _open(selected) {
    const path = this._recordPath(selected);
    if (!existsSync(path)) return null;
    const raw = readFileSync(path, "utf8");
    let record;
    try { record = JSON.parse(raw); } catch { throw new Error("replay ledger record is unreadable"); }
    if (canonicalJson(record) !== raw) throw new Error("replay ledger record is not canonical bytes");
    closedCanonicalObject(record, ["schema_version", "replay_scope_digest", "replay_envelope_digest", "result"], "replay ledger record");
    if (record.schema_version !== REPLAY_SCHEMA_VERSION || record.replay_scope_digest !== replayScopeDigestV1(selected)) throw new Error("replay ledger record has a conflicting commit scope");
    closedCanonicalObject(record.result, REPLAY_RESULT_FIELDS, "replay ledger result");
    const stored = record.result.canonical_input;
    const persisted = selectCanonicalAuthorityInputV1({
      commitId: stored.commit_id, workspaceUid: stored.workspace_uid, projectUidOrNull: stored.project_uid_or_null,
      worktreeUid: stored.worktree_uid, revisionId: stored.revision_id, expectedRegistryRevisionId: stored.expected_registry_revision_id,
      expectedBaseSnapshotUidOrNull: stored.expected_base_snapshot_uid_or_null, expectedPublicationUidOrNull: stored.expected_publication_uid_or_null,
      inputDeltas: stored.input_deltas
    });
    const digest = canonicalAuthorityInputDigestV1(persisted);
    if (digest !== record.replay_envelope_digest || digest !== record.result.replay_envelope_digest) throw new Error("replay ledger record envelope digest verification failed");
    return replayResultV1(persisted, digest);
  }

  record(selected) {
    const lock = this._acquire(selected);
    try {
      const prior = this._open(selected);
      const digest = canonicalAuthorityInputDigestV1(selected);
      if (prior) {
        if (prior.replay_envelope_digest !== digest) throw new Error("replay denied: commit scope already has a different canonical envelope");
        return prior;
      }
      const result = replayResultV1(selected, digest);
      atomicCanonicalWrite(this._recordPath(selected), Object.freeze({
        schema_version: REPLAY_SCHEMA_VERSION, replay_scope_digest: replayScopeDigestV1(selected), replay_envelope_digest: digest, result
      }));
      return result;
    } finally { this._release(lock); }
  }
}

export class TargetInventoryStoreV1 {
  constructor(token, state) {
    if (token !== STORE_CONSTRUCTOR_TOKEN) throw new TypeError("TargetInventoryStoreV1 is constructed only by KnowledgeCompilerCommitPublisherV1");
    STORE_STATE.set(this, state);
    Object.freeze(this);
  }

  publishAuthorityInventoryV1({ permit, build }) {
    const state = STORE_STATE.get(this);
    const permitState = PERMIT_STATE.get(permit);
    if (!state || !permitState || permitState.store !== this || permitState.used) {
      throw new TypeError("AuthorityInventoryPublishPermitV1 is not authorized for this TargetInventoryStoreV1");
    }
    if (!build || typeof build !== "object" || Array.isArray(build) || build !== permitState.build) {
      throw new TypeError("ProductionInventoryBuildV1 must be the private transaction build");
    }
    permitState.used = true;
    return freezeDeep({ authority_store_id: state.store_id, canonical_input: permitState.canonical_input });
  }
}

class PublisherPermitIssuerV1 {
  constructor(token, state) {
    if (token !== ISSUER_CONSTRUCTOR_TOKEN) throw new TypeError("PublisherPermitIssuerV1 is composition-root private");
    ISSUER_STATE.set(this, state);
  }

  mintForCommit(canonicalInput, build) {
    const state = ISSUER_STATE.get(this);
    if (!state || !build || typeof build !== "object") throw new TypeError("publisher permit issue denied");
    const permit = Object.freeze({ schema_version: 1, permit_uid: `spkp1-${randomBytes(16).toString("hex")}` });
    PERMIT_STATE.set(permit, { store: state.store, canonical_input: canonicalInput, build, used: false });
    return permit;
  }
}

/** Public entry: it never exposes the store, issuer, permit, or build. */
export function createKnowledgeCompilerCommitPublisherV1({ registry, snapshotStore }) {
  if (!isWorkspaceRegistryV1(registry)) throw new TypeError("registry must be a composition-root branded WorkspaceRegistryV1");
  if (!isImmutableSnapshotStoreV1(snapshotStore)) throw new TypeError("snapshotStore must be a composition-root branded ImmutableSnapshotStoreV1");
  const state = { store_id: `tis1-${randomBytes(16).toString("hex")}` };
  const store = new TargetInventoryStoreV1(STORE_CONSTRUCTOR_TOKEN, state);
  state.store = store;
  const issuer = new PublisherPermitIssuerV1(ISSUER_CONSTRUCTOR_TOKEN, state);
  const replayLedger = new ReplayLedgerV1(snapshotStore.cacheRoot);
  return Object.freeze({
    selectCommitInputV1(input) {
      const selected = selectCanonicalAuthorityInputV1(input);
      if (selected.workspace_uid !== registry.workspace_uid) throw new TypeError("CommitInputV1 workspace does not match this composition root");
      // P1 exercises private issuance; P2 consumes it only after build materialization.
      issuer.mintForCommit(selected, Object.freeze({ p1: true }));
      return freezeDeep({ canonical_input: selected, replay_envelope_digest: canonicalAuthorityInputDigestV1(selected) });
    },
    recordReplayEnvelopeV1(input) {
      const selected = selectCanonicalAuthorityInputV1(input);
      if (selected.workspace_uid !== registry.workspace_uid) throw new TypeError("CommitInputV1 workspace does not match this composition root");
      return replayLedger.record(selected);
    }
  });
}
