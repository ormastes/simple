import assert from "node:assert/strict";
import { generateKeyPairSync } from "node:crypto";
import test from "node:test";

import {
  createAuthorizationPort,
  createCanonicalReadAuthorizationPort,
  isVerifiedCanonicalReadGrantV1,
  signCanonicalReadReceiptV1,
} from "../../src/core/authorization.js";

const BASE64URL = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

const binding = Object.freeze({
  receiptVersion: "v1",
  authorityKeyId: "read-key",
  authorityKeyEpoch: 1,
  normalizedAliasUriOrNull: null,
  canonicalUri: "spipe://project/p/artifact/A-1",
  workspaceUid: "W-1",
  projectUidOrNull: "P-1",
  targetKind: "artifact",
  targetUid: "A-1",
  snapshotUid: "V-1",
  revisionId: "r1",
  viewKind: "artifact",
  normalizedLogicalPath: "",
  selectorDigest: "sha256:" + "a".repeat(64),
  effectiveScopeDigest: "sha256:" + "b".repeat(64),
  orderingVersion: "v1",
  pageLimitOrNull: null,
  policyVersion: "policy-1",
  decision: "allow",
  issuedAtMs: 99,
  expiresAtMs: 101,
  issuerKeyId: "read-key",
  revocationEpoch: 0,
});

function harness() {
  const keys = generateKeyPairSync("ed25519");
  const port = createCanonicalReadAuthorizationPort({
    publicKeys: { "read-key": keys.publicKey },
    allowedKeyEpochs: { "read-key": 1 },
    now: () => 100,
  });
  return { keys, port };
}

function nonCanonicalUnusedBits(value) {
  const index = BASE64URL.indexOf(value.at(-1));
  return value.slice(0, -1) + BASE64URL[(index & 0b110000) | 1];
}

test("canonical producer receipt is accepted by the canonical authorization port", () => {
  const { keys, port } = harness();
  const receipt = signCanonicalReadReceiptV1(binding, keys.privateKey);

  assert.equal(receipt.receiptVersion, "v1");
  assert.match(receipt.signature, /^[A-Za-z0-9_-]+$/);
  const grant = port.verifyCanonicalReadReceiptV1(receipt, binding, 100);
  assert.ok(isVerifiedCanonicalReadGrantV1(grant));
  const unsignedReceipt = { ...receipt };
  delete unsignedReceipt.signature;
  assert.deepEqual(grant.binding, unsignedReceipt);
});

test("canonical authorization rejects altered signatures and migrated versions", () => {
  const { keys, port } = harness();
  const receipt = signCanonicalReadReceiptV1(binding, keys.privateKey);
  const alteredSignature = receipt.signature[0] === "A" ? `B${receipt.signature.slice(1)}` : `A${receipt.signature.slice(1)}`;

  assert.equal(port.verifyCanonicalReadReceiptV1({ ...receipt, signature: alteredSignature }, binding, 100), null);
  assert.equal(port.verifyCanonicalReadReceiptV1({ ...receipt, receiptVersion: 1 }, binding, 100), null);
  assert.throws(() => signCanonicalReadReceiptV1({ ...binding, receiptVersion: 1 }, keys.privateKey), /invalid canonical read receipt v1/);
});

test("canonical read verification rejects malformed base64url spellings", () => {
  const { keys, port } = harness();
  const receipt = signCanonicalReadReceiptV1(binding, keys.privateKey);

  for (const signature of ["A", `${receipt.signature}=`, nonCanonicalUnusedBits(receipt.signature)]) {
    assert.equal(port.verifyCanonicalReadReceiptV1({ ...receipt, signature }, binding, 100), null);
  }
});

test("createAuthorizationPort cursor verification preserves canonical base64url compatibility", () => {
  const readKeys = generateKeyPairSync("ed25519");
  const cursorKeys = generateKeyPairSync("ed25519");
  const policy = {
    policyVersion: 1,
    currentReceiptRevocationEpoch: 0,
    currentAuthorityKeyId: "cursor-key",
    maxTtlMs: 500,
    keyRecords: [{
      authorityKeyId: "cursor-key", algorithm: "ed25519", authorityKeyEpoch: 1,
      issuerKeyId: "cursor-issuer", publicVerificationKey: cursorKeys.publicKey.export({ type: "spki", format: "der" }).toString("base64"),
      status: "current", activateAtMs: 0, graceUntilMsOrNull: null,
      revokedAtMsOrNull: null, revocationEpochAtRevocationOrNull: null,
    }],
    rotationRecords: [],
  };
  const store = { load: () => JSON.parse(JSON.stringify(policy)) };
  const port = createAuthorizationPort({
    publicKeys: { "read-key": readKeys.publicKey },
    cursorPolicyStore: store,
    cursorKeyProvider: { getPrivateKey: () => cursorKeys.privateKey },
    now: () => 100,
  });
  const expected = port.createExpectedReadBindingV1(binding);
  const read = signCanonicalReadReceiptV1(binding, readKeys.privateKey);
  const grant = port.verifyCanonicalReadReceiptV1(read, expected, 100);
  assert.ok(grant);

  const cursor = port.issueCursorReceiptV1(grant, { pagePosition: ["item-1"], requestedExpiresAtMs: 101 }, 100);
  assert.ok(cursor);
  assert.ok(port.verifyCursorReceiptV1(cursor, grant, 100));
  for (const signature of ["A", `${cursor.signature}=`, nonCanonicalUnusedBits(cursor.signature)]) {
    assert.equal(port.verifyCursorReceiptV1({ ...cursor, signature }, grant, 100), null);
  }
});
