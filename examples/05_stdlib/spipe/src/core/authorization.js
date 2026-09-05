import { createHash, sign, timingSafeEqual, verify } from "node:crypto";
import { existsSync, mkdirSync, openSync, readFileSync, renameSync, writeFileSync, fsyncSync, closeSync } from "node:fs";
import { dirname } from "node:path";

import { canonicalJson, freezeDeep } from "../storage/canonical.js";
import { assertCanonicalUid } from "../model/identity.js";
import { expectedReadBindingClaimsV1 } from "../view/snapshot_authority.js";
import { isReadReceiptPolicyStore } from "../storage/read_receipt_policy_store.js";

const TRUSTED_PORTS = new WeakSet();
const VERIFIED_READ_GRANTS = new WeakSet();
const VERIFIED_CURSOR_GRANTS = new WeakSet();

const READ_RECEIPT_V1_FIELDS = Object.freeze([
  "receiptVersion", "authorityKeyId", "authorityKeyEpoch", "normalizedAliasUriOrNull",
  "canonicalUri", "workspaceUid", "projectUidOrNull", "targetKind", "targetUid",
  "snapshotUid", "revisionId", "viewKind", "normalizedLogicalPath", "selectorDigest",
  "effectiveScopeDigest", "orderingVersion", "pageLimitOrNull", "policyVersion",
  "decision", "issuedAtMs", "expiresAtMs", "receiptUid", "issuerKeyId", "revocationEpoch"
]);

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
export function createAuthorizationPort({ publicKeys, revokedReceiptUids = [], now = () => Date.now(), canonicalReadPolicy = null, canonicalReadPolicyStore = null } = {}) {
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
        const expected = expectedReadBindingClaimsV1(expectedBinding);
        const activePolicy = canonicalReadPolicyStore === null ? readPolicy : canonicalReadPolicyStore.read().policy;
        if (!expected || !activePolicy || activePolicy.policyVersion !== expected.policyVersion || !exactFields(receipt, READ_FIELDS)) return null;
        const payload = readPayload(receipt);
        if (!validReadPayload(payload) || payload.policyVersion !== activePolicy.policyVersion || typeof receipt.signature !== "string" || !/^[A-Za-z0-9_-]+$/.test(receipt.signature)) return null;
        const unsignedForId = { ...payload, receiptUid: undefined };
        const expectedUid = readIdentity(unsignedForId);
        if (payload.receiptUid !== expectedUid || activePolicy.revokedReceiptUids.includes(payload.receiptUid)) return null;
        const key = new Map(activePolicy.keys.map((item) => [item.authorityKeyId, item])).get(payload.authorityKeyId);
        if (!key || key.issuerKeyId !== payload.issuerKeyId || key.algorithm !== "ed25519" || key.epoch !== payload.authorityKeyEpoch ||
            key.status !== "current" || payload.revocationEpoch !== activePolicy.revocationEpoch) return null;
        const publicKey = keys.get(payload.issuerKeyId);
        if (!publicKey || !verify(null, readSigningBytes(payload), publicKey, Buffer.from(receipt.signature, "base64url"))) return null;
        if (!Number.isSafeInteger(clockNowMs) || payload.issuedAtMs > clockNowMs || payload.expiresAtMs <= clockNowMs) return null;
        for (const field of Object.keys(expected)) {
          if (field === "worktreeUid" || field === "authorityInstanceUid" || field === "authorityManifestDigest") continue;
          if (payload[field] !== expected[field]) return null;
        }
        const grant = Object.freeze({});
        READ_GRANTS.set(grant, freezeDeep({ ...payload, worktreeUid: expected.worktreeUid, authorityInstanceUid: expected.authorityInstanceUid, authorityManifestDigest: expected.authorityManifestDigest }));
        return grant;
      } catch { return null; }
    }
  });
  TRUSTED_PORTS.add(port);
  return port;
}

export function isVerifiedReadGrantV1(value) { return READ_GRANTS.has(value); }
export function verifiedReadGrantClaimsV1(value) { return READ_GRANTS.get(value) ?? null; }

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
      if (payload.receiptVersion !== 1 || payload.decision !== "allow" ||
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
          !verify(null, readReceiptV1Bytes(payload, cursor), publicKey, Buffer.from(receipt.signature, "base64"))) return null;
      const grant = freezeDeep({ type: cursor ? "verified_cursor_grant_v1" : "verified_read_grant_v1", binding: payload });
      (cursor ? VERIFIED_CURSOR_GRANTS : VERIFIED_READ_GRANTS).add(grant);
      return grant;
    } catch { return null; }
  }

  function signReceipt(binding, privateKey, cursor = false) {
    const payload = readReceiptV1Payload(binding, { cursor });
    if (payload.receiptVersion !== 1 || !privateKey || !algorithms.has(privateKey.asymmetricKeyType)) throw new TypeError("invalid canonical read receipt v1");
    const signedPayload = { ...payload, receiptUid: readReceiptUid(payload, cursor) };
    return freezeDeep({ ...signedPayload, ...(cursor ? { lastSortKey: payload.lastSortKey } : {}), signature: sign(null, readReceiptV1Bytes(signedPayload, cursor), privateKey).toString("base64") });
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
  if (payload.receiptVersion !== 1 || privateKey?.asymmetricKeyType !== "ed25519") throw new TypeError("invalid canonical read receipt v1");
  const signedPayload = { ...payload, receiptUid: readReceiptUid(payload) };
  return freezeDeep({ ...signedPayload, signature: sign(null, readReceiptV1Bytes(signedPayload), privateKey).toString("base64") });
}

export function isVerifiedCanonicalReadGrantV1(grant) {
  return Boolean(grant && VERIFIED_READ_GRANTS.has(grant));
}

export function isVerifiedCursorGrantV1(grant) {
  return Boolean(grant && VERIFIED_CURSOR_GRANTS.has(grant));
}
