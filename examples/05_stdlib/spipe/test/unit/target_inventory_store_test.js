import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { spawn } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import {
  TargetInventoryStoreV1, canonicalAuthorityInputDigestV1,
  createKnowledgeCompilerCommitPublisherV1, selectCanonicalAuthorityInputV1
} from "../../src/core/knowledge_compiler_commit_publisher.js";
import { ImmutableSnapshotStore } from "../../src/storage/snapshot_store.js";
import { canonicalJson } from "../../src/storage/canonical.js";
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

function journalPaths(cacheRoot) {
  const root = join(cacheRoot, "shared", "spipe", "authority-publication-v1");
  const name = readdirSync(join(root, "records")).at(0);
  return { root, record: join(root, "records", name) };
}
function journalLockPath(cacheRoot, commitId = "commit-1") {
  const scope = createHash("sha256").update(canonicalJson({ schema_version: 1, commit_id: commitId })).digest("hex");
  return join(cacheRoot, "shared", "spipe", "authority-publication-v1", "locks", `${scope}.lock`);
}
function writeCorruptOwner(cacheRoot, pid) {
  const lock = journalLockPath(cacheRoot);
  mkdirSync(join(cacheRoot, "shared", "spipe", "authority-publication-v1", "locks"), { recursive: true, mode: 0o700 });
  writeFileSync(lock, canonicalJson({ schema_version: 1, pid, nonce: "corrupt-persisted-owner" }), { mode: 0o600 });
  return lock;
}
function waitFor(predicate, message) {
  return new Promise(async (resolve, reject) => {
    for (let attempt = 0; attempt < 500; attempt += 1) {
      if (predicate()) return resolve();
      await new Promise((next) => setTimeout(next, 2));
    }
    reject(new Error(message));
  });
}
const publisherModule = new URL("../../src/core/knowledge_compiler_commit_publisher.js", import.meta.url).pathname;
const registryModule = new URL("../../src/workspace/registry.js", import.meta.url).pathname;
const snapshotModule = new URL("../../src/storage/snapshot_store.js", import.meta.url).pathname;
// Prerequisites are constructed before readiness.  The parent deletes the
// cache root while children retain those branded inputs; publisher construction
// then races the journal's truly absent-root path.
const publisherProgram = `
  import { createKnowledgeCompilerCommitPublisherV1 } from ${JSON.stringify(publisherModule)};
  import { WorkspaceRegistry } from ${JSON.stringify(registryModule)};
  import { ImmutableSnapshotStore } from ${JSON.stringify(snapshotModule)};
  import { existsSync, mkdirSync, writeFileSync } from "node:fs";
  const pause = () => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 2);
  const registry = new WorkspaceRegistry({ root: process.env.ROOT, workspaceUid: process.env.WORKSPACE });
  const snapshots = new ImmutableSnapshotStore({ cacheRoot: process.env.ROOT });
  if (process.env.BARRIER) { mkdirSync(process.env.BARRIER, { recursive: true }); writeFileSync(process.env.BARRIER + "/" + process.env.NAME + ".ready", "ready"); while (!existsSync(process.env.BARRIER + "/start")) pause(); }
  const publisher = createKnowledgeCompilerCommitPublisherV1({ registry, snapshotStore: snapshots });
  process.stdout.write(JSON.stringify(publisher.selectCommitInputV1(JSON.parse(process.env.INPUT))));
`;
function launchPublisher({ cacheRoot, inputValue = input(), barrier = null, name = null, extraEnv = {} }) {
  const child = spawn(process.execPath, ["--input-type=module", "--eval", publisherProgram], { env: { ...process.env, ...extraEnv, ROOT: cacheRoot, WORKSPACE, INPUT: JSON.stringify(inputValue), ...(barrier ? { BARRIER: barrier, NAME: name } : {}) } });
  const completed = new Promise((resolve, reject) => { let stdout = "", stderr = ""; child.stdout.on("data", (part) => { stdout += part; }); child.stderr.on("data", (part) => { stderr += part; }); child.on("error", reject); child.on("exit", (code, signal) => resolve({ code, signal, stdout, stderr })); });
  return { child, completed };
}

test("P2 keeps journal construction and reconstitution capability out of the module surface", async () => {
  const surface = await import("../../src/core/knowledge_compiler_commit_publisher.js");
  for (const name of ["createAuthorityPublicationJournalV1", "createPrivateAuthorityJournalV1", "reconstitutePersistedAuthorityInputV1"]) assert.equal(name in surface, false, `${name} must be lexical-private`);
});

test("P2 denies changed persisted canonical fields before duplicate record creation", () => {
  const fixture = root();
  try {
    const publisher = createKnowledgeCompilerCommitPublisherV1(fixture);
    publisher.selectCommitInputV1(input());
    const before = readFileSync(journalPaths(fixture.cacheRoot).record, "utf8");
    for (const changed of [input({ revisionId: "git:def" }), input({ expectedBaseSnapshotUidOrNull: "base-1", expectedPublicationUidOrNull: "pub-1" }), input({ inputDeltas: [{ nested: { title: "changed" } }] })]) assert.throws(() => publisher.selectCommitInputV1(changed), /replay denied/);
    assert.equal(readFileSync(journalPaths(fixture.cacheRoot).record, "utf8"), before);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P2 process replay denial binds revision, expected IDs, and recursive deltas", async () => {
  const fixture = root();
  try {
    const winner = input();
    assert.equal((await launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: winner }).completed).code, 0);
    const before = readFileSync(journalPaths(fixture.cacheRoot).record, "utf8");
    for (const loser of [input({ revisionId: "git:other" }), input({ expectedBaseSnapshotUidOrNull: "base-x", expectedPublicationUidOrNull: "publication-x" }), input({ inputDeltas: [{ deeply: { nested: ["different"] } }] })]) {
      const result = await launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: loser }).completed;
      assert.notEqual(result.code, 0); assert.match(result.stderr, /replay denied/); assert.equal(readFileSync(journalPaths(fixture.cacheRoot).record, "utf8"), before);
    }
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P2 concurrent process contenders persist one envelope and deny the other", async () => {
  const fixture = root();
  try {
    const barrier = join(fixture.cacheRoot, "barrier");
    const leftInput = input({ revisionId: "git:left" }), rightInput = input({ revisionId: "git:right" });
    const left = launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: leftInput, barrier, name: "left" });
    const right = launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: rightInput, barrier, name: "right" });
    await waitFor(() => existsSync(join(barrier, "left.ready")) && existsSync(join(barrier, "right.ready")), "contenders did not reach barrier");
    writeFileSync(join(barrier, "start"), "go");
    const results = await Promise.all([left.completed, right.completed]);
    const successes = results.filter((r) => r.code === 0), failures = results.filter((r) => r.code !== 0);
    assert.equal(successes.length, 1); assert.equal(failures.length, 1); assert.match(failures[0].stderr, /replay denied/);
    const persisted = JSON.parse(readFileSync(journalPaths(fixture.cacheRoot).record, "utf8")).result.canonical_input;
    const winningInput = persisted.revision_id === "git:left" ? leftInput : rightInput;
    const losingInput = persisted.revision_id === "git:left" ? rightInput : leftInput;
    assert.equal((await launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: winningInput }).completed).code, 0);
    const retry = await launchPublisher({ cacheRoot: fixture.cacheRoot, inputValue: losingInput }).completed;
    assert.notEqual(retry.code, 0); assert.match(retry.stderr, /replay denied/);
  } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
});

test("P2 first-use races the absent journal root after retained prerequisite construction", async () => {
  const parent = mkdtempSync(join(tmpdir(), "spipe-p2-parent-")), cacheRoot = join(parent, "absent-cache-root"), barrier = join(parent, "barrier");
  try {
    const left = launchPublisher({ cacheRoot, barrier, name: "left" }), right = launchPublisher({ cacheRoot, barrier, name: "right" });
    await waitFor(() => existsSync(join(barrier, "left.ready")) && existsSync(join(barrier, "right.ready")), "first-use workers did not reach barrier");
    rmSync(cacheRoot, { recursive: true, force: true }); assert.equal(existsSync(cacheRoot), false, "journal cache root must be absent at release");
    writeFileSync(join(barrier, "start"), "go");
    const results = await Promise.all([left.completed, right.completed]);
    assert.equal(results[0].code, 0, results[0].stderr); assert.equal(results[1].code, 0, results[1].stderr);
    assert.deepEqual(JSON.parse(results[0].stdout), JSON.parse(results[1].stdout));
  } finally { rmSync(parent, { recursive: true, force: true }); }
});

test("P2 process recovery claims corrupt stale owners exclusively without unsafe PID probes", async () => {
  for (const pid of [0, -1, 1.5, "not-a-pid", Number.MAX_SAFE_INTEGER + 1]) {
    const fixture = root();
    try {
      const lock = writeCorruptOwner(fixture.cacheRoot, pid);
      const left = launchPublisher({ cacheRoot: fixture.cacheRoot });
      const right = launchPublisher({ cacheRoot: fixture.cacheRoot });
      const results = await Promise.all([left.completed, right.completed]);
      for (const result of results) assert.equal(result.code, 0, `invalid persisted PID ${String(pid)} must recover without process-group liveness probing: ${result.stderr}`);
      assert.deepEqual(JSON.parse(results[0].stdout), JSON.parse(results[1].stdout));
      assert.equal(existsSync(lock), false, `invalid persisted PID ${String(pid)} must be removed only by the exclusive reclaimer`);
      const persisted = JSON.parse(readFileSync(journalPaths(fixture.cacheRoot).record, "utf8"));
      assert.equal(persisted.result.canonical_input.commit_id, "commit-1");
    } finally { rmSync(fixture.cacheRoot, { recursive: true, force: true }); }
  }
});
