import assert from "node:assert/strict";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import {
  TargetInventoryStoreV1, canonicalAuthorityInputDigestV1,
  createKnowledgeCompilerCommitPublisherV1, selectCanonicalAuthorityInputV1
} from "../../src/core/knowledge_compiler_commit_publisher.js";
import { ImmutableSnapshotStore } from "../../src/storage/snapshot_store.js";
import { WorkspaceRegistry } from "../../src/workspace/registry.js";

const WORKSPACE = "W-000000000000000000000000000000B1";

function root() {
  const cacheRoot = mkdtempSync(join(tmpdir(), "spipe-target-inventory-"));
  const registry = new WorkspaceRegistry({ root: cacheRoot, workspaceUid: WORKSPACE });
  return { cacheRoot, registry, snapshotStore: new ImmutableSnapshotStore({ cacheRoot }) };
}

function input(overrides = {}) {
  return {
    commitId: "commit-1", workspaceUid: WORKSPACE, projectUidOrNull: null,
    worktreeUid: "W-000000000000000000000000000000B2", revisionId: "git:abc",
    expectedRegistryRevisionId: "rr-1", expectedBaseSnapshotUidOrNull: null,
    expectedPublicationUidOrNull: null, inputDeltas: [], ...overrides
  };
}

test("P1 composition root admits only the internal canonical-input path", () => {
  const fixture = root();
  try {
    const publisher = createKnowledgeCompilerCommitPublisherV1(fixture);
    const result = publisher.selectCommitInputV1(input());
    assert.equal(result.canonical_input.commit_id, "commit-1");
    assert.match(result.replay_envelope_digest, /^sha256:[0-9a-f]{64}$/);
    assert.deepEqual(Object.keys(publisher), ["selectCommitInputV1"]);
    assert.throws(() => new TargetInventoryStoreV1(), /KnowledgeCompilerCommitPublisherV1/);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P1 rejects instanceof/prototype and structural composition inputs", () => {
  const fixture = root();
  try {
    const fakeRegistry = Object.create(WorkspaceRegistry.prototype);
    fakeRegistry.workspace_uid = WORKSPACE;
    const fakeSnapshots = Object.create(ImmutableSnapshotStore.prototype);
    assert.throws(() => createKnowledgeCompilerCommitPublisherV1({ registry: fakeRegistry, snapshotStore: fixture.snapshotStore }), /branded/);
    assert.throws(() => createKnowledgeCompilerCommitPublisherV1({ registry: fixture.registry, snapshotStore: fakeSnapshots }), /branded/);
    assert.throws(() => createKnowledgeCompilerCommitPublisherV1({ registry: {}, snapshotStore: {} }), /branded/);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P1 exposes no journal, store, issuer, permit, or caller-selected root path", () => {
  const fixture = root();
  try {
    const publisher = createKnowledgeCompilerCommitPublisherV1(fixture);
    for (const name of ["issuer", "store", "permit", "publishAuthorityInventoryV1", "authorityPublicationJournal"]) {
      assert.equal(name in publisher, false);
    }
    assert.throws(() => selectCanonicalAuthorityInputV1({ ...input(), authorityPublicationJournal: {} }), /closed schema/);
    assert.throws(() => selectCanonicalAuthorityInputV1({ ...input(), permit: JSON.parse('{"permit_uid":"spkp1-forged"}') }), /closed schema/);
    assert.throws(() => selectCanonicalAuthorityInputV1({ ...input(), aggregateRoot: "caller-root" }), /closed schema/);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P1 canonical envelope NFC-normalizes every accepted nested string value", () => {
  const composed = input({ inputDeltas: [{ title: "é", nested: ["Å", { text: "café" }] }] });
  const decomposed = input({ inputDeltas: [{ title: "e\u0301", nested: ["A\u030a", { text: "cafe\u0301" }] }] });
  const selectedComposed = selectCanonicalAuthorityInputV1(composed);
  const selectedDecomposed = selectCanonicalAuthorityInputV1(decomposed);
  assert.deepEqual(selectedDecomposed.input_deltas, selectedComposed.input_deltas);
  assert.equal(selectedDecomposed.input_deltas[0].title, "é");
  assert.equal(selectedDecomposed.input_deltas[0].nested[0], "Å");
  assert.equal(selectedDecomposed.input_deltas[0].nested[1].text, "café");
  assert.equal(canonicalAuthorityInputDigestV1(decomposed), canonicalAuthorityInputDigestV1(composed));
});

test("P1 canonical envelope is strict and deterministic over accepted JSON input", () => {
  const selected = selectCanonicalAuthorityInputV1(input({ inputDeltas: [{ z: 1, a: 2 }] }));
  assert.equal(selected.input_deltas[0].a, 2);
  assert.equal(canonicalAuthorityInputDigestV1(input({ inputDeltas: [{ a: 2, z: 1 }] })), canonicalAuthorityInputDigestV1(input({ inputDeltas: [{ z: 1, a: 2 }] })));
  assert.throws(() => selectCanonicalAuthorityInputV1(input({ inputDeltas: [{ a: undefined }] })), /undefined/);
  assert.throws(() => selectCanonicalAuthorityInputV1(input({ inputDeltas: [1n] })), /plain JSON/);
  const withSymbol = input();
  withSymbol[Symbol("permit")] = "forged";
  assert.throws(() => selectCanonicalAuthorityInputV1(withSymbol), /symbols/);
  const accessor = input();
  Object.defineProperty(accessor, "commitId", { enumerable: true, get: () => "changed" });
  assert.throws(() => selectCanonicalAuthorityInputV1(accessor), /data properties/);
  const sparse = input({ inputDeltas: new Array(1) });
  assert.throws(() => selectCanonicalAuthorityInputV1(sparse), /dense/);
  const augmented = input({ inputDeltas: [] });
  augmented.inputDeltas.root = "forged";
  assert.throws(() => selectCanonicalAuthorityInputV1(augmented), /dense/);
  assert.throws(() => selectCanonicalAuthorityInputV1(input({ inputDeltas: [{ "e\u0301": 1, "é": 2 }] })), /unique after NFC/);
  assert.doesNotThrow(() => selectCanonicalAuthorityInputV1(input({ inputDeltas: [JSON.parse('{"__proto__":1}')] })));
});
