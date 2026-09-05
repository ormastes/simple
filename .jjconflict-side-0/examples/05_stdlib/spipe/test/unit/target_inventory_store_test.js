import assert from "node:assert/strict";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawn } from "node:child_process";
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
    assert.deepEqual(Object.keys(publisher), ["selectCommitInputV1", "recordReplayEnvelopeV1"]);
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

test("P2 commit-scoped replay returns one durable envelope and denies changed trusted bindings", () => {
  const fixture = root();
  try {
    const publisher = createKnowledgeCompilerCommitPublisherV1(fixture);
    const first = publisher.recordReplayEnvelopeV1(input());
    assert.deepEqual(publisher.recordReplayEnvelopeV1(input()), first);
    for (const changed of [
      { revisionId: "git:def" }, { expectedRegistryRevisionId: "rr-2" },
      { expectedBaseSnapshotUidOrNull: "B-2", expectedPublicationUidOrNull: "P-2" },
      { inputDeltas: [{ change: "different" }] }, { worktreeUid: "W-000000000000000000000000000000B3" }
    ]) assert.throws(() => publisher.recordReplayEnvelopeV1(input(changed)), /replay denied/);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

function childProcess(source, environment) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, ["--input-type=module", "--eval", source], { env: environment });
    let output = "";
    let errors = "";
    child.stdout.on("data", (chunk) => { output += chunk; });
    child.stderr.on("data", (chunk) => { errors += chunk; });
    child.on("error", reject);
    child.on("exit", (code) => code === 0 ? resolve(output) : reject(new Error(errors || `child exited ${code}`)));
  });
}

test("P2 two independent processes create an absent nested ledger after a barrier without EEXIST", async () => {
  const fixture = root();
  try {
    const modulePath = new URL("../../src/core/knowledge_compiler_commit_publisher.js", import.meta.url).pathname;
    const registryPath = new URL("../../src/workspace/registry.js", import.meta.url).pathname;
    const snapshotsPath = new URL("../../src/storage/snapshot_store.js", import.meta.url).pathname;
    const barrier = join(fixture.cacheRoot, "barrier");
    mkdirSync(barrier);
    const source = `
      import { existsSync, writeFileSync } from "node:fs";
      import { createKnowledgeCompilerCommitPublisherV1 } from ${JSON.stringify(modulePath)};
      import { WorkspaceRegistry } from ${JSON.stringify(registryPath)};
      import { ImmutableSnapshotStore } from ${JSON.stringify(snapshotsPath)};
      const wait = (path) => { while (!existsSync(path)) Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 2); };
      writeFileSync(process.env.SPIPE_BARRIER + "/" + process.env.SPIPE_NAME + ".ready", "ready");
      wait(process.env.SPIPE_BARRIER + "/start");
      const registry = new WorkspaceRegistry({ root: process.env.SPIPE_ROOT, workspaceUid: process.env.SPIPE_WORKSPACE });
      const snapshotStore = new ImmutableSnapshotStore({ cacheRoot: process.env.SPIPE_ROOT });
      const publisher = createKnowledgeCompilerCommitPublisherV1({ registry, snapshotStore });
      process.stdout.write(JSON.stringify(publisher.recordReplayEnvelopeV1(JSON.parse(process.env.SPIPE_INPUT))));
    `;
    const environment = { ...process.env, SPIPE_ROOT: fixture.cacheRoot, SPIPE_WORKSPACE: WORKSPACE, SPIPE_INPUT: JSON.stringify(input()), SPIPE_BARRIER: barrier };
    // The parent owns only the barrier. Neither child may construct a publisher
    // before start, so both race the absent shared/spipe/replay ancestors.
    const left = childProcess(source, { ...environment, SPIPE_NAME: "left" });
    const right = childProcess(source, { ...environment, SPIPE_NAME: "right" });
    for (let attempt = 0; attempt < 1_000 && !(existsSync(join(barrier, "left.ready")) && existsSync(join(barrier, "right.ready"))); attempt += 1) {
      await new Promise((resolve) => setTimeout(resolve, 2));
    }
    assert.equal(existsSync(join(barrier, "left.ready")) && existsSync(join(barrier, "right.ready")), true, "both children reached barrier before publisher construction");
    writeFileSync(join(barrier, "start"), "start");
    const [leftResult, rightResult] = await Promise.all([left, right]);
    assert.deepEqual(JSON.parse(leftResult), JSON.parse(rightResult));
    const replayRoot = join(fixture.cacheRoot, "shared", "spipe", "commit-replay-v1");
    for (const directory of [
      join(fixture.cacheRoot, "shared"), join(fixture.cacheRoot, "shared", "spipe"),
      replayRoot, join(replayRoot, "records"), join(replayRoot, "locks")
    ]) assert.equal(existsSync(directory), true);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P2 recovers a killed durable owner receipt without changing the replay result", async () => {
  const fixture = root();
  try {
    const publisher = createKnowledgeCompilerCommitPublisherV1(fixture);
    const expected = publisher.recordReplayEnvelopeV1(input());
    const replayRoot = join(fixture.cacheRoot, "shared", "spipe", "commit-replay-v1");
    const record = readdirSync(join(replayRoot, "records"))[0];
    const lock = join(replayRoot, "locks", `${record.slice(0, -5)}.lock`);
    const source = `
      import { closeSync, fsyncSync, openSync, writeFileSync } from "node:fs";
      const fd = openSync(process.env.SPIPE_LOCK, "wx", 0o600);
      writeFileSync(fd, '{"pid":' + process.pid + ',"schema_version":1}'); fsyncSync(fd); closeSync(fd);
      process.stdout.write("ready"); setInterval(() => {}, 1_000);
    `;
    const child = spawn(process.execPath, ["--input-type=module", "--eval", source], { env: { ...process.env, SPIPE_LOCK: lock } });
    await new Promise((resolve, reject) => {
      let output = "";
      child.stdout.on("data", (chunk) => { output += chunk; if (output === "ready") resolve(); });
      child.on("error", reject);
      child.on("exit", (code) => { if (output !== "ready") reject(new Error(`owner exited ${code}`)); });
    });
    child.kill("SIGKILL");
    await new Promise((resolve) => child.once("exit", resolve));
    assert.deepEqual(publisher.recordReplayEnvelopeV1(input()), expected);
    assert.equal(existsSync(lock), false);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});
