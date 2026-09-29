import assert from "node:assert/strict";
import test from "node:test";
import { generateKeyPairSync, verify } from "node:crypto";
import { existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { sha256Hex, canonicalJson } from "../../src/storage/canonical.js";
import { createSnapshotAuthorityPortV1 } from "../../src/view/snapshot_authority.js";
import { createAuthorizationPort, isVerifiedReadGrantV1, signCanonicalReadReceiptV1 } from "../../src/core/authorization.js";
import { createReadReceiptPolicyStore } from "../../src/storage/read_receipt_policy_store.js";

const ID = "01K3R8G3N70ZMT43W6QJ7YHX4P";
const W = `W-${ID}`, P = `P-${ID}`, WT = `WT-${ID}`, AI = `AI-${ID}`;
const digest = (value) => sha256Hex(canonicalJson(value));
const hash = (letter) => letter.repeat(64);

function fixture() {
  const entry = { targetKind: "artifact", targetUid: `A-${ID}`, locator: "opaque", contentDigest: hash("d") };
  const inventoryBare = { version: "v1", scopeKind: "project", workspaceUid: W, projectUidOrNull: P, worktreeUid: WT,
    baseSnapshotUid: "base-1", revisionId: "r1", entries: [entry], aliasIndex: { "spipe://skill": { targetKind: "artifact", targetUid: entry.targetUid } },
    projectionRoot: hash("e"), contributingProjectRoots: [] };
  const inventory = { ...inventoryBare, rootDigest: digest(inventoryBare) };
  const authorityBare = { baseSnapshotUid: "base-1", targetInventoryRoot: inventory.rootDigest,
    workspaceUid: W, projectUidOrNull: P, worktreeUid: WT, revisionId: "r1", scopeKind: "project", contributingProjectRoots: [] };
  const authority = { snapshotUid: `spka1-${digest(authorityBare)}`, ...authorityBare };
  const port = createSnapshotAuthorityPortV1({
    workspaceRegistry: { workspace_uid: W, worktree: (uid) => uid === WT ? { project_uid: P } : null },
    snapshotStore: { read: (uid) => uid === "base-1" ? { project_uid: P, worktree_uid: WT, revision_id: "r1" } : null },
    targetInventoryStore: { readAuthorityManifest: (uid) => uid === authority.snapshotUid ? authority : null, readTargetInventory: (root) => root === inventory.rootDigest ? inventory : null },
    authorityInstanceUid: AI
  });
  const view = port.openBoundSnapshot({ workspaceUid: W, projectUidOrNull: P, worktreeUid: WT, snapshotUid: authority.snapshotUid, revisionId: "r1" });
  const target = port.resolveCanonicalTarget(view, { targetKind: "artifact", targetUid: entry.targetUid });
  const request = { authorityKeyId: "read-key", authorityKeyEpoch: 1, normalizedAliasUriOrNull: null, canonicalUri: `spipe://project/p/artifact/${entry.targetUid}`,
    workspaceUid: W, projectUidOrNull: P, targetKind: "artifact", targetUid: entry.targetUid, snapshotUid: authority.snapshotUid, revisionId: "r1",
    viewKind: "artifact", normalizedLogicalPath: "", selectorDigest: hash("a"), effectiveScopeDigest: hash("b"), orderingVersion: "v1", pageLimitOrNull: null, policyVersion: "policy-1" };
  return { port, view, target, request };
}

test("Wave5C sealed authority binding admits only proved target and exact direct read", () => {
  const { port, view, target, request } = fixture();
  const binding = port.createExpectedReadBindingV1(view, target, request);
  assert.ok(binding);
  const keys = generateKeyPairSync("ed25519");
  const auth = createAuthorizationPort({ publicKeys: { issuer: keys.publicKey }, now: () => 100,
    canonicalReadPolicy: { policyVersion: "policy-1", revocationEpoch: 4, revokedReceiptUids: [], keys: [{ authorityKeyId: "read-key", issuerKeyId: "issuer", algorithm: "ed25519", epoch: 1, status: "current" }] } });
  const receipt = signCanonicalReadReceiptV1({ ...request, receiptVersion: "v1", decision: "allow", issuedAtMs: 99, expiresAtMs: 101, issuerKeyId: "issuer", revocationEpoch: 4 }, keys.privateKey);
  const unsigned = { ...receipt }; delete unsigned.signature;
  assert.equal(verify(null, Buffer.concat([Buffer.from("spipe-uri-read-v1\0"), Buffer.from(canonicalJson(unsigned))]), keys.publicKey, Buffer.from(receipt.signature, "base64url")), true, "wire domain contains one NUL byte");
  const grant = auth.verifyCanonicalReadReceiptV1(receipt, binding, 100);
  assert.ok(isVerifiedReadGrantV1(grant));
});

test("Wave5C rejects structural, cross-binding, stale, key epoch and revoked read admission", () => {
  const { port, view, target, request } = fixture();
  const binding = port.createExpectedReadBindingV1(view, target, request);
  const keys = generateKeyPairSync("ed25519");
  const policy = { policyVersion: "policy-1", revocationEpoch: 4, revokedReceiptUids: [], keys: [{ authorityKeyId: "read-key", issuerKeyId: "issuer", algorithm: "ed25519", epoch: 1, status: "current" }] };
  const receipt = signCanonicalReadReceiptV1({ ...request, receiptVersion: "v1", decision: "allow", issuedAtMs: 99, expiresAtMs: 101, issuerKeyId: "issuer", revocationEpoch: 4 }, keys.privateKey);
  const auth = createAuthorizationPort({ publicKeys: { issuer: keys.publicKey }, canonicalReadPolicy: policy });
  assert.equal(auth.verifyCanonicalReadReceiptV1(receipt, { ...request }, 100), null, "duck binding denied");
  const wrong = port.createExpectedReadBindingV1(view, target, { ...request, pageLimitOrNull: 20 });
  assert.equal(auth.verifyCanonicalReadReceiptV1(receipt, wrong, 100), null, "direct/null page binding is exact");
  assert.equal(auth.verifyCanonicalReadReceiptV1(receipt, binding, 101), null, "expired denied");
  const epochAuth = createAuthorizationPort({ publicKeys: { issuer: keys.publicKey }, canonicalReadPolicy: { ...policy, revocationEpoch: 5 } });
  assert.equal(epochAuth.verifyCanonicalReadReceiptV1(receipt, binding, 100), null, "revocation epoch denied");
  const revokedAuth = createAuthorizationPort({ publicKeys: { issuer: keys.publicKey }, canonicalReadPolicy: { ...policy, revokedReceiptUids: [receipt.receiptUid] } });
  assert.equal(revokedAuth.verifyCanonicalReadReceiptV1(receipt, binding, 100), null, "receipt revocation denied");
  const foreign = signCanonicalReadReceiptV1({ ...request, authorityKeyEpoch: 2, receiptVersion: "v1", decision: "allow", issuedAtMs: 99, expiresAtMs: 101, issuerKeyId: "issuer", revocationEpoch: 4 }, keys.privateKey);
  assert.equal(auth.verifyCanonicalReadReceiptV1(foreign, binding, 100), null, "key epoch mismatch denied");
});

test("Wave5C authority rejects foreign snapshots, malformed inventories and alias candidates cannot render", () => {
  const { port, view } = fixture();
  assert.equal(port.openBoundSnapshot({ workspaceUid: W, projectUidOrNull: P, worktreeUid: WT, snapshotUid: "spka1-not-the-authority", revisionId: "r2" }), null);
  const candidate = port.resolveCanonicalAlias(view, { normalizedAliasUri: "spipe://skill" });
  assert.ok(candidate);
  assert.equal(port.createExpectedReadBindingV1(view, candidate, {}), null);
  assert.equal(port.resolveCanonicalTarget({}, { targetKind: "artifact", targetUid: `A-${ID}` }), null);
});

test("Wave5C durable issuer policy survives restart and has one CAS winner", () => {
  const root = mkdtempSync(join(tmpdir(), "spipe-read-policy-"));
  const policy = { policyVersion: "policy-1", revocationEpoch: 4, revokedReceiptUids: [], keys: [{ authorityKeyId: "read-key", issuerKeyId: "issuer", algorithm: "ed25519", epoch: 1, status: "current" }] };
  try {
    const first = createReadReceiptPolicyStore({ path: join(root, "policy.sdn"), initialPolicy: policy });
    const baseline = first.read();
    const second = createReadReceiptPolicyStore({ path: join(root, "policy.sdn") });
    const winner = first.compareAndSwap(baseline.digest, { ...policy, revocationEpoch: 5 });
    assert.ok(winner);
    assert.equal(second.compareAndSwap(baseline.digest, { ...policy, revocationEpoch: 6 }), null, "stale writer loses");
    const restarted = createReadReceiptPolicyStore({ path: join(root, "policy.sdn") });
    assert.equal(restarted.read().policy.revocationEpoch, 5);
    assert.equal(restarted.compareAndSwap(restarted.read().digest, { ...policy, revocationEpoch: 3 }), null, "revocation cannot roll back");
    writeFileSync(join(root, "policy.sdn.lock"), "foreign");
    assert.equal(restarted.compareAndSwap(restarted.read().digest, { ...policy, revocationEpoch: 6 }), null, "active peer lock wins");
    assert.equal(existsSync(join(root, "policy.sdn.lock")), true, "failed contender cannot remove a peer lock");
  } finally { rmSync(root, { recursive: true, force: true }); }
});
