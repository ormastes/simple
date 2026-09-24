import { createHash, createPublicKey, sign, timingSafeEqual, verify } from "node:crypto";
import { existsSync, mkdirSync, openSync, readFileSync, renameSync, writeFileSync, fsyncSync, closeSync } from "node:fs";
import { dirname } from "node:path";

import { canonicalJson, freezeDeep } from "../storage/canonical.js";
import { assertCanonicalUid } from "../model/identity.js";
import { expectedReadBindingClaimsV1 } from "../view/snapshot_authority.js";
import { isReadReceiptPolicyStore } from "../storage/read_receipt_policy_store.js";

const TRUSTED_PORTS = new WeakSet();
const VERIFIED_READ_GRANTS = new WeakSet();
const VERIFIED_CURSOR_GRANTS = new WeakSet();
const EXPECTED_READ_BINDINGS = new WeakMap();
const READ_GRANT_CLAIMS = new WeakMap();

const READ_RECEIPT_V1_FIELDS = Object.freeze([
  "receiptVersion", "authorityKeyId", "authorityKeyEpoch", "normalizedAliasUriOrNull",
  "canonicalUri", "workspaceUid", "projectUidOrNull", "targetKind", "targetUid",
  "snapshotUid", "revisionId", "viewKind", "normalizedLogicalPath", "selectorDigest",
  "effectiveScopeDigest", "orderingVersion", "pageLimitOrNull", "policyVersion",
  "decision", "issuedAtMs", "expiresAtMs", "receiptUid", "issuerKeyId", "revocationEpoch"
]);
// The admitted V1 wire ABI is shared by both receipt producers and consumers:
// string "v1" plus unpadded RFC 4648 base64url signatures.  An older,
// unadmitted draft used numeric 1 and standard base64; do not accept both
// spellings because that would make one named schema have two signing domains.
const CANONICAL_READ_RECEIPT_V1 = "v1";
const BASE64URL_SIGNATURE = /^[A-Za-z0-9_-]+$/;

function isCanonicalBase64Url(value) {
  if (typeof value !== "string" || !BASE64URL_SIGNATURE.test(value)) return false;
  try {
    return Buffer.from(value, "base64url").toString("base64url") === value;
  } catch {
    return false;
  }
}

function readReceiptV1Payload(input, { cursor = false } = {}) {
  const value = {};
  for (const field of READ_RECEIPT_V1_FIELDS) value[field] = input[field] ?? null;
  if (cursor) value.lastSortKey = input.lastSortKey ?? null;
  return value;
}

function readReceiptV1Bytes(payload, cursor = false) {
  return Buffer.from(`${cursor ? "spipe-uri-cursor-v1" : "spipe-uri-read-v1"}\0${canonicalJson(payload)}`);
}

function readReceiptUid(payload, cursor = false) {
  return `D-${createHash("sha256").update(readReceiptV1Bytes({ ...payload, receiptUid: null }, cursor)).digest("hex").slice(0, 32).toUpperCase()}`;
}

function exactBinding(payload, expected) {
  return Object.keys(expected).every((field) => payload[field] === expected[field]);
}

const READ_FIELDS = Object.freeze([...READ_RECEIPT_V1_FIELDS, "signature"]);

function exactFields(value, fields) {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const names = Object.keys(value).sort();
  const expected = [...fields].sort();
  if (names.length !== expected.length || names.some((name, index) => name !== expected[index])) return false;
  return fields.every((field) => {
    const descriptor = Object.getOwnPropertyDescriptor(value, field);
    return descriptor?.enumerable === true && Object.hasOwn(descriptor, "value") && !Object.hasOwn(descriptor, "get");
  });
}

function readPayload(input) {
  const payload = {};
  for (const field of READ_RECEIPT_V1_FIELDS) payload[field] = input[field];
  return payload;
}

function validReadPayload(payload) {
  return payload.receiptVersion === "v1" && payload.decision === "allow" &&
    typeof payload.authorityKeyId === "string" && Number.isSafeInteger(payload.authorityKeyEpoch) && payload.authorityKeyEpoch >= 0 &&
    (payload.normalizedAliasUriOrNull === null || typeof payload.normalizedAliasUriOrNull === "string") &&
    typeof payload.canonicalUri === "string" && typeof payload.workspaceUid === "string" &&
    (payload.projectUidOrNull === null || typeof payload.projectUidOrNull === "string") &&
    typeof payload.targetKind === "string" && typeof payload.targetUid === "string" &&
    typeof payload.snapshotUid === "string" && typeof payload.revisionId === "string" &&
    typeof payload.viewKind === "string" && typeof payload.normalizedLogicalPath === "string" &&
    typeof payload.selectorDigest === "string" && typeof payload.effectiveScopeDigest === "string" &&
    typeof payload.orderingVersion === "string" && (payload.pageLimitOrNull === null || Number.isSafeInteger(payload.pageLimitOrNull)) &&
    (typeof payload.policyVersion === "string" || Number.isSafeInteger(payload.policyVersion)) &&
    Number.isSafeInteger(payload.issuedAtMs) && Number.isSafeInteger(payload.expiresAtMs) &&
    typeof payload.receiptUid === "string" && typeof payload.issuerKeyId === "string" && Number.isSafeInteger(payload.revocationEpoch);
}

function readIdentity(payload) { return readReceiptUid(payload); }
function readSigningBytes(payload) { return readReceiptV1Bytes(payload); }
function legacyReadReceiptUid(payload) {
  const unsigned = { ...payload, receiptUid: undefined };
  return createHash("sha256").update("spipe-uri-read-id-v1\0", "utf8").update(canonicalJson(unsigned), "utf8").digest("hex");
}

function cursorSigningBytes(payload) {
  return Buffer.from(`spipe-uri-cursor-v1\0${canonicalJson(payload)}`);
}

function digest(value) {
  return createHash("sha256").update(canonicalJson(value)).digest("hex");
}

function unsignedPayload(input) {
  return {
    schema: 1, issuer_key_id: String(input.issuer_key_id),
    project_uid: String(input.project_uid), worktree_uid: String(input.worktree_uid),
    revision_id: String(input.revision_id), source_set_hash: String(input.source_set_hash),
    trust_scope: String(input.trust_scope), principal: String(input.principal),
    capability: String(input.capability), policy_hash: String(input.policy_hash),
    policy_version: String(input.policy_version), decided_at_ms: Number(input.decided_at_ms),
    expires_at_ms: Number(input.expires_at_ms), audit_evidence_hash: String(input.audit_evidence_hash)
  };
}

function unsignedEdgePayload(input) {
  return {
    schema: 1, receipt_kind: "edge_acceptance", issuer_key_id: String(input.issuer_key_id),
    edge_uid: String(input.edge_uid), acceptance_subject_hash: String(input.acceptance_subject_hash),
    from_uid: String(input.from_uid), to_uid: String(input.to_uid), origin: String(input.origin),
    status: String(input.status), project_uid: String(input.project_uid),
    worktree_uid: String(input.worktree_uid), input_snapshot_uid: String(input.input_snapshot_uid),
    policy_hash: String(input.policy_hash), policy_version: Number(input.policy_version),
    capability: String(input.capability), decided_at_ms: Number(input.decided_at_ms),
    expires_at_ms: Number(input.expires_at_ms), audit_evidence_hash: String(input.audit_evidence_hash)
  };
}

export function signTrustReceipt(input, privateKey) {
  const unsigned = unsignedPayload(input);
  const receipt_uid = `D-${digest(unsigned).slice(0, 32).toUpperCase()}`;
  const payload = { ...unsigned, receipt_uid };
  return freezeDeep({ ...payload, signature: sign(null, Buffer.from(canonicalJson(payload)), privateKey).toString("base64") });
}

export function signEdgeAcceptanceReceipt(input, privateKey) {
  const unsigned = unsignedEdgePayload(input);
  const receipt_uid = `D-${digest(unsigned).slice(0, 32).toUpperCase()}`;
  const payload = { ...unsigned, receipt_uid };
  return freezeDeep({ ...payload, signature: sign(null, Buffer.from(canonicalJson(payload)), privateKey).toString("base64") });
}

/** Verification-only capability injected by the trusted composition root. */
export function createAuthorizationPort({ publicKeys, revokedReceiptUids = [], now = () => Date.now(), canonicalReadPolicy = null, canonicalReadPolicyStore = null, cursorPolicyStore = null, cursorKeyProvider = null } = {}) {
  const keys = new Map(Object.entries(publicKeys ?? {}));
  if (!keys.size) throw new TypeError("AuthorizationPort requires trusted public keys");
  const revoked = new Set(revokedReceiptUids);
  if (canonicalReadPolicy !== null && canonicalReadPolicyStore !== null) throw new TypeError("canonical read policy has one source");
  if (canonicalReadPolicyStore !== null && !isReadReceiptPolicyStore(canonicalReadPolicyStore)) throw new TypeError("canonical read policy store is not trusted");
  const readPolicy = canonicalReadPolicy === null ? null : freezeDeep(JSON.parse(canonicalJson(canonicalReadPolicy)));
  if (readPolicy !== null && (!exactFields(readPolicy, ["policyVersion", "revocationEpoch", "keys", "revokedReceiptUids"]) ||
      !Number.isSafeInteger(readPolicy.revocationEpoch) || !Array.isArray(readPolicy.keys) || !Array.isArray(readPolicy.revokedReceiptUids))) {
    throw new TypeError("canonical read policy is invalid");
  }
  function cursorPolicy() {
    if (!cursorPolicyStore || typeof cursorPolicyStore.load !== "function") return null;
    return cursorPolicyStore.load();
  }
  function cursorKey(policy, id) { return policy?.keyRecords?.find((item) => item.authorityKeyId === id) ?? null; }
  function cursorPositionValid(position) {
    return Array.isArray(position) && position.length > 0 && position.every((value) =>
      (typeof value === "string" && value.length > 0) || (typeof value === "number" && Number.isSafeInteger(value)));
  }
  function createExpectedReadBindingV1(binding) {
    if (!binding || typeof binding !== "object" || Array.isArray(binding)) return null;
    const outward = Object.freeze({ ...binding });
    const claims = { ...binding, pageLimitOrNull: binding.pageLimitOrNull ?? binding.pageLimit ?? null };
    delete claims.pageLimit;
    EXPECTED_READ_BINDINGS.set(outward, Object.freeze(claims));
    return outward;
  }
  function issueCursorReceiptV1(grant, request = {}, clockNowMs = now()) {
    try {
      const claims = READ_GRANT_CLAIMS.get(grant); const policy = cursorPolicy();
      if (!claims || !policy || !cursorPositionValid(request.pagePosition) || !Number.isSafeInteger(clockNowMs)) return null;
      const key = cursorKey(policy, policy.currentAuthorityKeyId);
      if (!key || !cursorKeyProvider || typeof cursorKeyProvider.getPrivateKey !== "function") return null;
      const privateKey = cursorKeyProvider.getPrivateKey({ authorityKeyId: key.authorityKeyId, algorithm: key.algorithm, purpose: "spipe-cursor-receipt-v1" });
      const requested = request.requestedExpiresAtMs;
      const maxTtl = Number.isSafeInteger(policy.maxTtlMs) ? policy.maxTtlMs : 0;
      const expiresAtMs = Number.isSafeInteger(requested) ? requested : clockNowMs + maxTtl;
      if (!privateKey || expiresAtMs <= clockNowMs || expiresAtMs > claims.expiresAtMs || expiresAtMs > clockNowMs + maxTtl) return null;
      const payload = { cursorVersion: "v1", binding: claims, pagePosition: request.pagePosition, issuedAtMs: clockNowMs, expiresAtMs,
        cursorAuthorityKeyId: key.authorityKeyId, cursorAuthorityKeyEpoch: key.authorityKeyEpoch, cursorRevocationEpoch: policy.currentReceiptRevocationEpoch };
      const signature = sign(null, cursorSigningBytes(payload), privateKey).toString("base64url");
      return freezeDeep({ ...payload, signature });
    } catch { return null; }
  }
  function verifyCursorReceiptV1(receipt, grant, clockNowMs = now()) {
    try {
      const claims = READ_GRANT_CLAIMS.get(grant); const policy = cursorPolicy();
      if (!claims || !policy || !receipt || typeof receipt !== "object" || !cursorPositionValid(receipt.pagePosition)) return null;
      if (receipt.cursorVersion !== "v1" || receipt.issuedAtMs > clockNowMs || receipt.expiresAtMs <= clockNowMs || receipt.expiresAtMs > claims.expiresAtMs) return null;
      if (receipt.cursorRevocationEpoch !== policy.currentReceiptRevocationEpoch) return null;
      if (canonicalJson(receipt.binding) !== canonicalJson(claims)) return null;
      const key = cursorKey(policy, receipt.cursorAuthorityKeyId);
      if (!key || (key.status !== "current" && !(key.status === "grace" && Number.isSafeInteger(key.graceUntilMs) && clockNowMs < key.graceUntilMs)) || key.authorityKeyEpoch !== receipt.cursorAuthorityKeyEpoch) return null;
      const publicKey = key.publicVerificationKey ? createPublicKey({ key: Buffer.from(key.publicVerificationKey, "base64"), format: "der", type: "spki" }) : null;
      if (!publicKey || !isCanonicalBase64Url(receipt.signature) || !verify(null, cursorSigningBytes({ cursorVersion: receipt.cursorVersion, binding: receipt.binding, pagePosition: receipt.pagePosition, issuedAtMs: receipt.issuedAtMs, expiresAtMs: receipt.expiresAtMs, cursorAuthorityKeyId: receipt.cursorAuthorityKeyId, cursorAuthorityKeyEpoch: receipt.cursorAuthorityKeyEpoch, cursorRevocationEpoch: receipt.cursorRevocationEpoch }), publicKey, Buffer.from(receipt.signature, "base64url"))) return null;
      return receipt;
    } catch { return null; }
  }
  function rotateCursorReceiptKeyV1(request, clockNowMs = now()) {
    try {
      const policy = cursorPolicy();
      if (!policy || !request || policy.policyVersion !== request.expectedPolicyVersion || policy.rotationRecords?.some((item) => item.rotationUid === request.rotationUid)) return policy?.rotationRecords?.some((item) => item.rotationUid === request.rotationUid) ? policy : null;
      const next = JSON.parse(JSON.stringify(policy));
      next.keyRecords.push({ authorityKeyId: request.newAuthorityKeyId, algorithm: request.newAlgorithm, authorityKeyEpoch: request.newAuthorityKeyEpoch, issuerKeyId: request.newIssuerKeyId, publicVerificationKey: request.newPublicVerificationKey, status: "pending", activateAtMs: request.activateAtMs, graceUntilMsOrNull: request.priorGraceUntilMs, revokedAtMsOrNull: null, revocationEpochAtRevocationOrNull: null });
      next.rotationRecords.push({ ...request }); next.policyVersion += 1;
      return cursorPolicyStore.compareAndSwap(policy.policyVersion, next) ? next : null;
    } catch { return null; }
  }
  function applyDueCursorReceiptKeyTransitionsV1(clockNowMs = now()) {
    try {
      const policy = cursorPolicy(); if (!policy) return null;
      const next = JSON.parse(JSON.stringify(policy)); let changed = false;
      for (const rotation of next.rotationRecords ?? []) {
        if (rotation.appliedAtMs === undefined && clockNowMs >= rotation.activateAtMs) {
          const old = next.keyRecords.find((item) => item.authorityKeyId === next.currentAuthorityKeyId); const fresh = next.keyRecords.find((item) => item.authorityKeyId === rotation.newAuthorityKeyId);
          if (old) { old.status = "grace"; old.graceUntilMs = rotation.priorGraceUntilMs; }
          if (fresh) fresh.status = "current";
          next.currentAuthorityKeyId = rotation.newAuthorityKeyId; rotation.appliedAtMs = clockNowMs; changed = true;
        }
        if (rotation.appliedAtMs !== undefined && rotation.revocationEpochAtPriorRevocation !== undefined && clockNowMs >= rotation.priorGraceUntilMs && next.currentReceiptRevocationEpoch < rotation.revocationEpochAtPriorRevocation) {
          const old = next.keyRecords.find((item) => item.authorityKeyId !== next.currentAuthorityKeyId && item.status === "grace"); if (old) { old.status = "revoked"; old.revokedAtMsOrNull = clockNowMs; old.revocationEpochAtRevocationOrNull = rotation.revocationEpochAtPriorRevocation; }
          next.currentReceiptRevocationEpoch = rotation.revocationEpochAtPriorRevocation; changed = true;
        }
      }
      if (!changed) return next;
      next.policyVersion += 1;
      return cursorPolicyStore.compareAndSwap(policy.policyVersion, next) ? next : null;
    } catch { return null; }
  }
  const port = Object.freeze({
    verifyTrustReceipt(receipt, expected) {
      try {
        if (!receipt || typeof receipt !== "object" || revoked.has(receipt.receipt_uid)) return null;
        const unsigned = unsignedPayload(receipt);
        const expectedUid = `D-${digest(unsigned).slice(0, 32).toUpperCase()}`;
        assertCanonicalUid(receipt.receipt_uid, "receipt_uid", ["D"]);
        if (!timingSafeEqual(Buffer.from(expectedUid), Buffer.from(receipt.receipt_uid))) return null;
        const payload = { ...unsigned, receipt_uid: receipt.receipt_uid };
        const publicKey = keys.get(unsigned.issuer_key_id);
        if (!publicKey || !verify(null, Buffer.from(canonicalJson(payload)), publicKey, Buffer.from(receipt.signature, "base64"))) return null;
        if (!Number.isSafeInteger(unsigned.decided_at_ms) || !Number.isSafeInteger(unsigned.expires_at_ms) ||
            unsigned.decided_at_ms > now() || unsigned.expires_at_ms <= now()) return null;
        for (const [field, value] of Object.entries(expected)) if (unsigned[field] !== value) return null;
        const requiredCapability = unsigned.trust_scope === "executable_policy" ? "policy.publish" : "trust_scope.assign";
        if (unsigned.capability !== requiredCapability) return null;
        return freezeDeep(payload);
      } catch {
        return null;
      }
    },
    verifyEdgeAcceptanceReceipt(receipt, expected) {
      try {
        if (!receipt || typeof receipt !== "object" || revoked.has(receipt.receipt_uid)) return null;
        const unsigned = unsignedEdgePayload(receipt);
        const expectedUid = `D-${digest(unsigned).slice(0, 32).toUpperCase()}`;
        assertCanonicalUid(receipt.receipt_uid, "receipt_uid", ["D"]);
        if (!timingSafeEqual(Buffer.from(expectedUid), Buffer.from(receipt.receipt_uid))) return null;
        const payload = { ...unsigned, receipt_uid: receipt.receipt_uid };
        const publicKey = keys.get(unsigned.issuer_key_id);
        if (!publicKey || !verify(null, Buffer.from(canonicalJson(payload)), publicKey, Buffer.from(receipt.signature, "base64"))) return null;
        if (!Number.isSafeInteger(unsigned.policy_version) || !Number.isSafeInteger(unsigned.decided_at_ms) ||
            !Number.isSafeInteger(unsigned.expires_at_ms) || unsigned.decided_at_ms > now() || unsigned.expires_at_ms <= now()) return null;
        for (const [field, value] of Object.entries(expected)) if (unsigned[field] !== value) return null;
        if (![["explicit", "trace.accept.explicit"], ["generated", "trace.accept.generated"]]
          .some(([origin, capability]) => unsigned.origin === origin && unsigned.capability === capability)) return null;
        if (unsigned.status !== "accepted") return null;
        return freezeDeep(payload);
      } catch {
        return null;
      }
    },
    verifyCanonicalReadReceiptV1(receipt, expectedBinding, clockNowMs = now()) {
      try {
        const expected = expectedReadBindingClaimsV1(expectedBinding) ?? EXPECTED_READ_BINDINGS.get(expectedBinding);
        const activePolicy = canonicalReadPolicyStore === null ? readPolicy :
          (typeof canonicalReadPolicyStore.read === "function" ? canonicalReadPolicyStore.read().policy : canonicalReadPolicyStore.load());
        if (!expected || !exactFields(receipt, READ_FIELDS)) return null;
        const payload = readPayload(receipt);
        if (!validReadPayload(payload) || (activePolicy && payload.policyVersion !== activePolicy.policyVersion) || typeof receipt.signature !== "string" || !/^[A-Za-z0-9_-]+$/.test(receipt.signature)) return null;
        const unsignedForId = { ...payload, receiptUid: undefined };
        const expectedUid = readIdentity(unsignedForId);
        if (payload.receiptUid !== expectedUid && payload.receiptUid !== legacyReadReceiptUid(payload)) return null;
        if (activePolicy && activePolicy.revokedReceiptUids.includes(payload.receiptUid)) return null;
        if (activePolicy) {
          const key = new Map(activePolicy.keys.map((item) => [item.authorityKeyId, item])).get(payload.authorityKeyId);
          if (!key || key.issuerKeyId !== payload.issuerKeyId || key.algorithm !== "ed25519" || key.epoch !== payload.authorityKeyEpoch ||
              key.status !== "current" || payload.revocationEpoch !== activePolicy.revocationEpoch) return null;
        }
        const publicKey = keys.get(payload.issuerKeyId);
        if (!publicKey || !isCanonicalBase64Url(receipt.signature) || !verify(null, readSigningBytes(payload), publicKey, Buffer.from(receipt.signature, "base64url"))) return null;
        if (!Number.isSafeInteger(clockNowMs) || payload.issuedAtMs > clockNowMs || payload.expiresAtMs <= clockNowMs) return null;
        for (const field of Object.keys(expected)) {
          if (field === "worktreeUid" || field === "authorityInstanceUid" || field === "authorityManifestDigest") continue;
          if (payload[field] !== expected[field]) return null;
        }
        const grant = freezeDeep({ ...payload, ...expected });
        VERIFIED_READ_GRANTS.add(grant);
        READ_GRANT_CLAIMS.set(grant, freezeDeep({ ...payload, ...expected }));
        return grant;
      } catch { return null; }
    },
    createExpectedReadBindingV1,
    issueCursorReceiptV1,
    verifyCursorReceiptV1,
    rotateCursorReceiptKeyV1,
    applyDueCursorReceiptKeyTransitionsV1
  });
  TRUSTED_PORTS.add(port);
  return port;
}

export function isVerifiedReadGrantV1(value) { return VERIFIED_READ_GRANTS.has(value); }
export function verifiedReadGrantClaimsV1(value) { return READ_GRANT_CLAIMS.get(value) ?? null; }

export function isTrustedAuthorizationPort(port) {
  return Boolean(port && TRUSTED_PORTS.has(port));
}

/**
 * Creates the Wave-5 read-admission boundary.  The returned port is branded in
 * this module: URI parsers may consume only its opaque grants, never a callback
 * that happens to look like a verifier.
 */
export function createCanonicalReadAuthorizationPort({
  publicKeys, privateKeys = {}, allowedKeyEpochs, revokedReceiptUids = [],
  revocationEpoch = 0, allowedIssuerKeyIds, algorithmAllowlist = ["ed25519"], now = () => Date.now()
} = {}) {
  const keys = new Map(Object.entries(publicKeys ?? {}));
  const privateKeyMap = new Map(Object.entries(privateKeys));
  const epochs = new Map(Object.entries(allowedKeyEpochs ?? {}));
  if (!keys.size || !epochs.size) throw new TypeError("CanonicalRead AuthorizationPort requires keys and key epochs");
  const revoked = new Set(revokedReceiptUids);
  const issuers = new Set(allowedIssuerKeyIds ?? keys.keys());
  const algorithms = new Set(algorithmAllowlist);

  function verifyReceipt(receipt, expectedBinding, clockNowMs, cursor = false) {
    try {
      if (!receipt || typeof receipt !== "object" || revoked.has(receipt.receiptUid)) return null;
      const permitted = new Set([...READ_RECEIPT_V1_FIELDS, ...(cursor ? ["lastSortKey"] : []), "signature"]);
      if (Object.keys(receipt).some((field) => !permitted.has(field))) return null;
      const payload = readReceiptV1Payload(receipt, { cursor });
      if (payload.receiptVersion !== CANONICAL_READ_RECEIPT_V1 || payload.decision !== "allow" ||
          !Number.isSafeInteger(clockNowMs) || !Number.isSafeInteger(payload.issuedAtMs) || !Number.isSafeInteger(payload.expiresAtMs) ||
          payload.issuedAtMs > clockNowMs || payload.expiresAtMs <= clockNowMs ||
          !Number.isSafeInteger(payload.authorityKeyEpoch) ||
          payload.authorityKeyEpoch !== epochs.get(payload.authorityKeyId) ||
          payload.revocationEpoch !== revocationEpoch ||
          payload.issuerKeyId !== payload.authorityKeyId || !issuers.has(payload.issuerKeyId) ||
          payload.receiptUid !== readReceiptUid(payload, cursor) ||
          !exactBinding(payload, expectedBinding)) return null;
      const publicKey = keys.get(payload.authorityKeyId);
      if (!publicKey || !algorithms.has(publicKey.asymmetricKeyType) || typeof receipt.signature !== "string" ||
          !isCanonicalBase64Url(receipt.signature) ||
          !verify(null, readReceiptV1Bytes(payload, cursor), publicKey, Buffer.from(receipt.signature, "base64url"))) return null;
      const grant = freezeDeep({ type: cursor ? "verified_cursor_grant_v1" : "verified_read_grant_v1", binding: payload });
      (cursor ? VERIFIED_CURSOR_GRANTS : VERIFIED_READ_GRANTS).add(grant);
      return grant;
    } catch { return null; }
  }

  function signReceipt(binding, privateKey, cursor = false) {
    const payload = readReceiptV1Payload(binding, { cursor });
    if (payload.receiptVersion !== CANONICAL_READ_RECEIPT_V1 || !privateKey || !algorithms.has(privateKey.asymmetricKeyType)) throw new TypeError("invalid canonical read receipt v1");
    const signedPayload = { ...payload, receiptUid: readReceiptUid(payload, cursor) };
    return freezeDeep({ ...signedPayload, ...(cursor ? { lastSortKey: payload.lastSortKey } : {}), signature: sign(null, readReceiptV1Bytes(signedPayload, cursor), privateKey).toString("base64url") });
  }

  const port = Object.freeze({
    verifyCanonicalReadReceiptV1(receipt, expectedBinding, clockNowMs = now()) {
      return verifyReceipt(receipt, expectedBinding, clockNowMs, false);
    },
    verifyCursorReceiptV1(receipt, expectedBinding, clockNowMs = now()) {
      return verifyReceipt(receipt, expectedBinding, clockNowMs, true);
    },
    signCursorReceiptV1(binding) {
      const privateKey = privateKeyMap.get(binding.authorityKeyId);
      return signReceipt(binding, privateKey, true);
    }
  });
  TRUSTED_PORTS.add(port);
  return port;
}

/** Test/composition-root helper; production callers should issue receipts off hot paths. */
export function signCanonicalReadReceiptV1(binding, privateKey) {
  const payload = readReceiptV1Payload(binding);
  if (payload.receiptVersion !== "v1" || privateKey?.asymmetricKeyType !== "ed25519") throw new TypeError("invalid canonical read receipt v1");
  const signedPayload = { ...payload, receiptUid: readReceiptUid(payload) };
  return freezeDeep({ ...signedPayload, signature: sign(null, readReceiptV1Bytes(signedPayload), privateKey).toString("base64url") });
}

export function isVerifiedCanonicalReadGrantV1(grant) {
  return Boolean(grant && VERIFIED_READ_GRANTS.has(grant));
}

export function isVerifiedCursorGrantV1(grant) {
  return Boolean(grant && VERIFIED_CURSOR_GRANTS.has(grant));
}
