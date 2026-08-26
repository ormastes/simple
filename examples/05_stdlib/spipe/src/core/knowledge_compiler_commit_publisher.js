import { randomBytes } from "node:crypto";

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
  return Object.freeze({
    selectCommitInputV1(input) {
      const selected = selectCanonicalAuthorityInputV1(input);
      if (selected.workspace_uid !== registry.workspace_uid) throw new TypeError("CommitInputV1 workspace does not match this composition root");
      // P1 exercises private issuance; P2 consumes it only after build materialization.
      issuer.mintForCommit(selected, Object.freeze({ p1: true }));
      return freezeDeep({ canonical_input: selected, replay_envelope_digest: canonicalAuthorityInputDigestV1(selected) });
    }
  });
}
