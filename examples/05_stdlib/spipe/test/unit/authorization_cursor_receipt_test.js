import assert from "node:assert/strict";
import { createHash, generateKeyPairSync, sign } from "node:crypto";
import test from "node:test";

import { canonicalJson } from "../../src/storage/canonical.js";
import { createAuthorizationPort } from "../../src/core/authorization.js";

const binding = Object.freeze({
  authorityKeyId: "cursor-key-1", authorityKeyEpoch: 1, authorityInstanceUid: "AI-1",
  authorityManifestDigest: "sha256:" + "a".repeat(64), normalizedAliasUriOrNull: null,
  canonicalUri: "spipe://project/p/artifact/A-1", workspaceUid: "WS-1", projectUidOrNull: "P-1",
  worktreeUid: "WT-1", targetKind: "artifact", targetUid: "A-1", snapshotUid: "V-1",
  revisionId: "r1", viewKind: "feature", normalizedLogicalPath: "feature/search",
  selectorDigest: "sha256:" + "b".repeat(64), effectiveScopeDigest: "sha256:" + "c".repeat(64),
  orderingVersion: "v1", pageLimit: 20, policyVersion: 1,
});

function readReceipt(expected, privateKey, issuedAtMs = 100, expiresAtMs = 1000) {
  const unsigned = {
    receiptVersion: "v1", authorityKeyId: expected.authorityKeyId, authorityKeyEpoch: expected.authorityKeyEpoch,
    normalizedAliasUriOrNull: expected.normalizedAliasUriOrNull, canonicalUri: expected.canonicalUri,
    workspaceUid: expected.workspaceUid, projectUidOrNull: expected.projectUidOrNull, targetKind: expected.targetKind,
    targetUid: expected.targetUid, snapshotUid: expected.snapshotUid, revisionId: expected.revisionId,
    viewKind: expected.viewKind, normalizedLogicalPath: expected.normalizedLogicalPath, selectorDigest: expected.selectorDigest,
    effectiveScopeDigest: expected.effectiveScopeDigest, orderingVersion: expected.orderingVersion,
    pageLimitOrNull: expected.pageLimit, policyVersion: expected.policyVersion, decision: "allow",
    issuedAtMs, expiresAtMs, issuerKeyId: "read-key", revocationEpoch: 0,
  };
  const receiptUid = createHash("sha256").update("spipe-uri-read-id-v1\0", "utf8")
    .update(canonicalJson(unsigned)).digest("hex");
  const payload = { ...unsigned, receiptUid };
  return { ...payload, signature: sign(null, Buffer.from(`spipe-uri-read-v1\0${canonicalJson(payload)}`), privateKey).toString("base64url") };
}

function harness() {
  const read = generateKeyPairSync("ed25519"); const cursor = generateKeyPairSync("ed25519");
  let stored = { policyVersion: 1, currentReceiptRevocationEpoch: 0, currentAuthorityKeyId: "cursor-key-1", maxTtlMs: 500,
    keyRecords: [{ authorityKeyId: "cursor-key-1", algorithm: "ed25519", authorityKeyEpoch: 1, issuerKeyId: "cursor-issuer-1", publicVerificationKey: cursor.publicKey.export({ type: "spki", format: "der" }).toString("base64"), status: "current", activateAtMs: 0, graceUntilMsOrNull: null, revokedAtMsOrNull: null, revocationEpochAtRevocationOrNull: null }], rotationRecords: [] };
  const store = { load: () => JSON.parse(JSON.stringify(stored)), compareAndSwap: (expected, next) => { if (stored.policyVersion !== expected) return false; stored = JSON.parse(JSON.stringify(next)); return true; } };
  const port = createAuthorizationPort({ publicKeys: { "read-key": read.publicKey }, cursorPolicyStore: store,
    cursorKeyProvider: { getPrivateKey: ({ authorityKeyId, algorithm, purpose }) => authorityKeyId === "cursor-key-1" && algorithm === "ed25519" && purpose === "spipe-cursor-receipt-v1" ? cursor.privateKey : null }, now: () => 200 });
  return { port, read, cursor, store, policy: () => stored };
}

test("cursor receipt signs the complete trusted read binding and rejects cross-binding or tampering", () => {
  const { port, read } = harness(); const expected = port.createExpectedReadBindingV1(binding);
  const grant = port.verifyCanonicalReadReceiptV1(readReceipt(expected, read.privateKey), expected, 200);
  assert.ok(grant); assert.equal(grant.worktreeUid, "WT-1"); assert.equal(grant.authorityManifestDigest, binding.authorityManifestDigest);
  const cursor = port.issueCursorReceiptV1(grant, { pagePosition: ["item-20", 20], requestedExpiresAtMs: 600 }, 200);
  assert.ok(cursor); assert.ok(port.verifyCursorReceiptV1(cursor, grant, 300));
  assert.equal(port.verifyCursorReceiptV1({ ...cursor, pagePosition: ["item-21", 21] }, grant, 300), null);
  const other = port.createExpectedReadBindingV1({ ...binding, normalizedLogicalPath: "feature/other" });
  const otherGrant = port.verifyCanonicalReadReceiptV1(readReceipt(other, read.privateKey), other, 200);
  assert.equal(port.verifyCursorReceiptV1(cursor, otherGrant, 300), null);
});

test("cursor issuance is bounded by read expiry, policy TTL, exact key policy, and branded grants", () => {
  const { port, read } = harness(); const expected = port.createExpectedReadBindingV1(binding);
  const grant = port.verifyCanonicalReadReceiptV1(readReceipt(expected, read.privateKey, 100, 550), expected, 200);
  assert.equal(port.issueCursorReceiptV1(grant, { pagePosition: ["x"], requestedExpiresAtMs: 701 }, 200), null);
  assert.equal(port.issueCursorReceiptV1(grant, { pagePosition: ["x"], requestedExpiresAtMs: 551 }, 200), null);
  assert.equal(port.issueCursorReceiptV1({ ...grant }, { pagePosition: ["x"], requestedExpiresAtMs: 500 }, 200), null);
  assert.equal(port.issueCursorReceiptV1(grant, { pagePosition: [{}], requestedExpiresAtMs: 500 }, 200), null);
});

test("rotation is CAS/idempotent and grace revocation invalidates old receipts", () => {
  const { port, read, store, policy } = harness(); const expected = port.createExpectedReadBindingV1(binding);
  const grant = port.verifyCanonicalReadReceiptV1(readReceipt(expected, read.privateKey, 100, 1000), expected, 200);
  const oldCursor = port.issueCursorReceiptV1(grant, { pagePosition: ["old"], requestedExpiresAtMs: 600 }, 200);
  const second = generateKeyPairSync("ed25519");
  const request = { rotationUid: "rotation-1", expectedPolicyVersion: 1, newAuthorityKeyId: "cursor-key-2", newAlgorithm: "ed25519", newAuthorityKeyEpoch: 2, newIssuerKeyId: "cursor-issuer-2", newPublicVerificationKey: second.publicKey.export({ type: "spki", format: "der" }).toString("base64"), activateAtMs: 300, priorGraceUntilMs: 400, revocationEpochAtPriorRevocation: 1 };
  assert.ok(port.rotateCursorReceiptKeyV1(request, 200)); assert.equal(port.rotateCursorReceiptKeyV1(request, 200).policyVersion, 2);
  assert.ok(port.applyDueCursorReceiptKeyTransitionsV1(300)); assert.equal(policy().keyRecords.find((key) => key.authorityKeyId === "cursor-key-1").status, "grace");
  assert.ok(port.verifyCursorReceiptV1(oldCursor, grant, 350));
  assert.ok(port.applyDueCursorReceiptKeyTransitionsV1(400)); assert.equal(port.verifyCursorReceiptV1(oldCursor, grant, 401), null);
  assert.equal(store.load().currentReceiptRevocationEpoch, 1);
});
