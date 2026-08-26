import { randomBytes } from "node:crypto";
import { closeSync, fsyncSync, linkSync, lstatSync, mkdirSync, openSync, readFileSync, renameSync, statSync, unlinkSync, writeFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";

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

/** P2 journal is lexically private: importers cannot choose its root or parser. */
const JVER = 1;
const JINPUT = Object.freeze(["schema_version", "commit_id", "workspace_uid", "project_uid_or_null", "worktree_uid", "revision_id", "expected_registry_revision_id", "expected_base_snapshot_uid_or_null", "expected_publication_uid_or_null", "input_deltas"]);
const JRECORD = Object.freeze(["schema_version", "replay_scope_digest", "replay_envelope_digest", "result"]);
const JRESULT = Object.freeze(["canonical_input", "canonical_input_bytes", "replay_envelope_digest"]);
const jdigest = (bytes) => `sha256:${sha256Hex(bytes)}`;
const jpause = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);

function reconstitutePersistedAuthorityInputV1(value) {
  return selectCanonicalAuthorityInputV1({
    commitId: value.commit_id, workspaceUid: value.workspace_uid, projectUidOrNull: value.project_uid_or_null,
    worktreeUid: value.worktree_uid, revisionId: value.revision_id, expectedRegistryRevisionId: value.expected_registry_revision_id,
    expectedBaseSnapshotUidOrNull: value.expected_base_snapshot_uid_or_null, expectedPublicationUidOrNull: value.expected_publication_uid_or_null,
    inputDeltas: value.input_deltas
  });
}
function jfsync(path) {
  if (process.env.SPIPE_AUTHORITY_JOURNAL_TEST_FSYNC_FAIL === "1") { delete process.env.SPIPE_AUTHORITY_JOURNAL_TEST_FSYNC_FAIL; const e = new Error("injected journal fsync failure"); e.code = "EIO"; throw e; }
  const fd = openSync(path, "r"); try { fsyncSync(fd); } finally { closeSync(fd); }
}
function jreal(path) { const s = lstatSync(path); if (!s.isDirectory() || s.isSymbolicLink()) throw new Error(`journal directory is not real: ${path}`); }
/** Every created entry (including cacheRoot/shared/spipe) is fsync-confirmed. */
function jensure(cacheRoot, leaf) {
  const suffix = relative(cacheRoot, leaf);
  if (suffix === ".." || suffix.startsWith(`..${process.platform === "win32" ? "\\\\" : "/"}`)) throw new Error("journal path escapes cache root");
  const paths = [cacheRoot, ...suffix.split(/[\\/]+/).filter(Boolean).map((_, i, all) => join(cacheRoot, ...all.slice(0, i + 1)))];
  for (const path of paths) {
    try { jreal(path); continue; } catch (e) { if (e?.code !== "ENOENT") throw e; }
    try { mkdirSync(path, 0o700); } catch (e) { if (e?.code !== "EEXIST") throw e; }
    jreal(path); jfsync(dirname(path)); jfsync(path);
  }
}
function jclosed(value, fields, label) {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new Error(`${label} must be an object`);
  const keys = Reflect.ownKeys(value);
  if (keys.length !== fields.length || keys.some((k) => typeof k !== "string" || !fields.includes(k))) throw new Error(`${label} has a non-closed schema`);
  for (const field of fields) { const d = Object.getOwnPropertyDescriptor(value, field); if (!d || !d.enumerable || !Object.hasOwn(d, "value") || d.get || d.set) throw new Error(`${label} must contain data fields only`); }
}
function jinput(value) {
  jclosed(value, JINPUT, "persisted canonical input");
  if (value.schema_version !== JVER) throw new Error("persisted canonical input has an unsupported schema version");
  for (const field of ["commit_id", "workspace_uid", "worktree_uid", "revision_id", "expected_registry_revision_id"]) if (typeof value[field] !== "string" || !value[field] || value[field] !== value[field].normalize("NFC")) throw new Error(`persisted canonical input ${field} is invalid`);
  for (const field of ["project_uid_or_null", "expected_base_snapshot_uid_or_null", "expected_publication_uid_or_null"]) if (value[field] !== null && (typeof value[field] !== "string" || !value[field] || value[field] !== value[field].normalize("NFC"))) throw new Error(`persisted canonical input ${field} is invalid`);
  if (!Array.isArray(value.input_deltas) || (value.expected_base_snapshot_uid_or_null === null) !== (value.expected_publication_uid_or_null === null)) throw new Error("persisted canonical input IDs/deltas are invalid");
  const bytes = canonicalJson(value); if (bytes !== canonicalJson(JSON.parse(bytes))) throw new Error("persisted canonical input is not canonical"); return bytes;
}
/**
 * A receipt may be parseable and canonical yet still be an invalid owner.
 * Keep that distinction: acquire can reclaim it under an exclusive, identity
 * bound claim, while an unreadable/non-canonical receipt remains fail-closed.
 * In particular, never pass 0, a negative value, fractions, or an unsafe
 * integer to process.kill: Node interprets non-positive PIDs as process-group
 * or broad process selectors.
 */
function jreceipt(path) {
  try {
    const bytes = readFileSync(path, "utf8"), value = JSON.parse(bytes);
    if (canonicalJson(value) !== bytes || !value || typeof value !== "object" || Array.isArray(value) || typeof value.nonce !== "string" || !value.nonce) return null;
    const pid_is_safe_positive_integer = Number.isSafeInteger(value.pid) && value.pid > 0;
    return Object.freeze({ bytes, digest: jdigest(bytes), stat: statSync(path), value, pid_is_safe_positive_integer });
  } catch { return null; }
}
function jsame(a, b) { return a.dev === b.dev && a.ino === b.ino; }
function jalive(pid) {
  if (!Number.isSafeInteger(pid) || pid <= 0) return false;
  try { process.kill(pid, 0); return true; } catch (e) { return e?.code === "EPERM"; }
}
function jownerAlive(receipt) { return receipt.pid_is_safe_positive_integer && jalive(receipt.value.pid); }
function jwrite(cacheRoot, path, value) { jensure(cacheRoot, dirname(path)); const temp = `${path}.tmp-${process.pid}-${randomBytes(16).toString("hex")}`; const fd = openSync(temp, "wx", 0o600); try { writeFileSync(fd, canonicalJson(value), "utf8"); fsyncSync(fd); } finally { closeSync(fd); } renameSync(temp, path); jfsync(dirname(path)); }
function createPrivateAuthorityJournalV1(cacheRoot) {
  const root = join(cacheRoot, "shared", "spipe", "authority-publication-v1"), records = join(root, "records"), locks = join(root, "locks");
  const scopeFor = (v) => sha256Hex(canonicalJson({ schema_version: JVER, commit_id: v.commit_id }));
  const record = (s) => join(records, `${s}.json`), lock = (s) => join(locks, `${s}.lock`), claim = (s) => join(locks, `${s}.reclaim`);
  function prepare() { jensure(cacheRoot, records); jensure(cacheRoot, locks); }
  function releaseClaim(path, mine) { const now = jreceipt(path); if (!now || now.digest !== mine.digest || !jsame(now.stat, mine.stat)) throw new Error("reclaimer claim ownership changed before release"); unlinkSync(path); jfsync(locks); }
  function reclaim(scope, observed) {
    const cp = claim(scope), lp = lock(scope), nonce = randomBytes(16).toString("hex");
    try { const fd = openSync(cp, "wx", 0o600); try { writeFileSync(fd, canonicalJson({ schema_version: JVER, pid: process.pid, nonce, lock_digest: observed.digest, lock_dev: observed.stat.dev, lock_ino: observed.stat.ino }), "utf8"); fsyncSync(fd); } finally { closeSync(fd); } jfsync(locks); } catch (e) { if (e?.code === "EEXIST") return false; throw e; }
    const mine = jreceipt(cp); if (!mine || mine.value.nonce !== nonce) throw new Error("reclaimer marker was not durably owned");
    try { const now = jreceipt(lp); if (!now || now.digest !== observed.digest || !jsame(now.stat, observed.stat) || jownerAlive(now)) return false; unlinkSync(lp); jfsync(locks); return true; } finally { releaseClaim(cp, mine); }
  }
  function acquire(scope) {
    const lp = lock(scope);
    for (;;) {
      const staging = join(locks, `.${scope}.${process.pid}.${randomBytes(16).toString("hex")}.owner`);
      try { const fd = openSync(staging, "wx", 0o600); try { writeFileSync(fd, canonicalJson({ schema_version: JVER, pid: process.pid, nonce: randomBytes(16).toString("hex") }), "utf8"); fsyncSync(fd); } finally { closeSync(fd); } linkSync(staging, lp); const mine = jreceipt(lp); if (!mine) throw new Error("visible journal lock lacks a valid owner receipt"); unlinkSync(staging); jfsync(locks); const ready = process.env.SPIPE_AUTHORITY_JOURNAL_TEST_HOLD_LOCK_READY; if (ready) { writeFileSync(ready, "owned", "utf8"); for (;;) jpause(10); } return mine; }
      catch (e) {
        try { unlinkSync(staging); } catch (cleanup) { if (cleanup?.code !== "ENOENT") throw cleanup; }
        if (e?.code !== "EEXIST") throw e;
        const seen = jreceipt(lp);
        if (!seen) {
          // A reclaimer may have removed the exact observed lock between our
          // failed O_EXCL link and this read.  That is a retry, not permission
          // to treat an unreadable extant owner as stale.
          try { lstatSync(lp); } catch (missing) { if (missing?.code === "ENOENT") { jpause(2); continue; } throw missing; }
          throw new Error("journal lock owner receipt is unreadable or non-canonical");
        }
        if (!jownerAlive(seen)) reclaim(scope, seen);
        jpause(2);
      }
    }
  }
  function release(scope, mine) { const now = jreceipt(lock(scope)); if (!now || now.digest !== mine.digest || !jsame(now.stat, mine.stat)) throw new Error("journal lock ownership changed before release"); unlinkSync(lock(scope)); jfsync(locks); }
  function open(scope) { let raw; try { raw = readFileSync(record(scope), "utf8"); } catch (e) { if (e?.code === "ENOENT") return null; throw e; } let value; try { value = JSON.parse(raw); } catch { throw new Error("journal record is unreadable"); } if (canonicalJson(value) !== raw) throw new Error("journal record bytes are not canonical"); jclosed(value, JRECORD, "journal record"); if (value.schema_version !== JVER || value.replay_scope_digest !== scope || typeof value.replay_envelope_digest !== "string") throw new Error("journal record scope/version mismatch"); jclosed(value.result, JRESULT, "journal record result"); const bytes = jinput(value.result.canonical_input), selected = reconstitutePersistedAuthorityInputV1(value.result.canonical_input); if (bytes !== canonicalJson(selected) || scopeFor(selected) !== scope || value.result.canonical_input_bytes !== bytes || value.result.replay_envelope_digest !== value.replay_envelope_digest || value.replay_envelope_digest !== jdigest(bytes)) throw new Error("journal record canonical input bytes/digest mismatch"); return freezeDeep({ canonical_input: selected, replay_envelope_digest: value.replay_envelope_digest }); }
  return Object.freeze({ record(selected) { prepare(); const scope = scopeFor(selected), mine = acquire(scope); try { const previous = open(scope), bytes = jinput(selected), envelope = jdigest(bytes); if (previous) { if (previous.replay_envelope_digest !== envelope || canonicalJson(previous.canonical_input) !== bytes) throw new Error("replay denied: commit scope already has a different canonical envelope"); return previous; } const result = Object.freeze({ canonical_input: selected, canonical_input_bytes: bytes, replay_envelope_digest: envelope }); jwrite(cacheRoot, record(scope), Object.freeze({ schema_version: JVER, replay_scope_digest: scope, replay_envelope_digest: envelope, result })); return freezeDeep({ canonical_input: selected, replay_envelope_digest: envelope }); } finally { release(scope, mine); } } });
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
  // Deliberately deferred initialization: constructing a publisher does not
  // touch cacheRoot, so process barriers can exercise true first-use races.
  const replayJournal = createPrivateAuthorityJournalV1(snapshotStore.cacheRoot);
  return Object.freeze({
    selectCommitInputV1(input) {
      const selected = selectCanonicalAuthorityInputV1(input);
      if (selected.workspace_uid !== registry.workspace_uid) throw new TypeError("CommitInputV1 workspace does not match this composition root");
      // P1 exercises private issuance; P2 consumes it only after build materialization.
      issuer.mintForCommit(selected, Object.freeze({ p1: true }));
      return replayJournal.record(selected);
    }
  });
}
