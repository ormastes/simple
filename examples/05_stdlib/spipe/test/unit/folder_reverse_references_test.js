import assert from "node:assert/strict";
import test from "node:test";

import { FolderReverseReferenceIndex, normalizeFolderBoundary } from "../../src/graph/index.js";

const snapshot = `spks1-${"1".repeat(64)}`;
const graphRoot = `sha256:${"2".repeat(64)}`;
const artifact = (uid, canonical_path) => ({ uid, canonical_path });
const edge = (uid, from_uid, to_uid, source_artifact_uid = null) => ({
  uid, from_uid, to_uid, edge_type: "links_to",
  provenance: { source_location: source_artifact_uid === null ? null : { source_artifact_uid } }
});

function fixture() {
  const target = `A-${"9".repeat(26)}`;
  const docsA = `A-${"1".repeat(26)}`;
  const docsNested = `A-${"2".repeat(26)}`;
  const docsPrefix = `A-${"3".repeat(26)}`;
  const sourceNode = `SY-${"4".repeat(26)}`;
  const index = new FolderReverseReferenceIndex({
    snapshot_uid: snapshot, graph_root: graphRoot,
    artifacts: [artifact(target, "doc/target.md"), artifact(docsA, "doc/a/one.md"), artifact(docsNested, "doc/a/nested/two.md"), artifact(docsPrefix, "doc/ab/three.md")],
    edges: [
      edge(`E-${"3".repeat(26)}`, docsPrefix, target),
      edge(`E-${"2".repeat(26)}`, sourceNode, target, docsNested),
      edge(`E-${"1".repeat(26)}`, docsA, target),
      edge(`E-${"8".repeat(26)}`, sourceNode, target),
      edge(`E-${"7".repeat(26)}`, docsA, docsNested)
    ],
    cursor_key: Buffer.alloc(32, 7)
  });
  return { index, target, docsA, docsNested };
}

test("folder reverse references enforce a deterministic path-segment boundary", () => {
  const { index, target, docsA, docsNested } = fixture();
  const result = index.query({ target_uid: target, folder_path: "doc/a" });
  assert.equal(result.complete, true);
  assert.equal(result.reason, null);
  assert.deepEqual(result.items.map((item) => item.source_artifact_uid), [docsNested, docsA]);
  assert.deepEqual(result.items.map((item) => item.source_path), ["doc/a/nested/two.md", "doc/a/one.md"]);
  assert.equal(Object.isFrozen(result), true);
  assert.equal(Object.isFrozen(result.items), true);
});

test("folder reverse references paginate within explicit work and result bounds", () => {
  const { index, target } = fixture();
  const first = index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 1 });
  assert.equal(first.complete, false);
  assert.equal(first.reason, "limit");
  assert.equal(first.counters.work_units, 1);
  const second = index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 1, cursor: first.next_cursor });
  assert.equal(second.items.length, 1);
  assert.notEqual(second.items[0].edge.uid, first.items[0].edge.uid);
  assert.throws(() => index.query({ target_uid: target, folder_path: "doc/ab", limit: 1, max_work_units: 1, cursor: first.next_cursor }), (error) => error.code === "SPK704");
  assert.throws(() => index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 1, cursor: `${first.next_cursor}x` }), (error) => error.code === "SPK704");
});

test("folder boundary and index limits fail closed", () => {
  assert.equal(normalizeFolderBoundary("."), "");
  for (const invalid of ["/doc", "doc/", "doc//a", "doc/../a", "doc\\a"]) {
    assert.throws(() => normalizeFolderBoundary(invalid), /canonical project-relative/);
  }
  assert.throws(() => new FolderReverseReferenceIndex({
    snapshot_uid: snapshot, graph_root: graphRoot,
    artifacts: [artifact(`A-${"1".repeat(26)}`, "doc/a.md")],
    edges: [edge(`E-${"1".repeat(26)}`, `A-${"1".repeat(26)}`, `A-${"2".repeat(26)}`)],
    max_indexed_edges: 0
  }), /between 1/);
});

test("target-specific index preserves results and rejects target drift", () => {
  const { target, docsA, docsNested } = fixture();
  const artifacts = [
    artifact(target, "doc/target.md"), artifact(docsA, "doc/a/one.md"),
    artifact(docsNested, "doc/a/nested/two.md")
  ];
  const edges = [edge(`E-${"2".repeat(26)}`, docsNested, target), edge(`E-${"1".repeat(26)}`, docsA, target)];
  const index = new FolderReverseReferenceIndex({
    snapshot_uid: snapshot, graph_root: graphRoot, artifacts, edges,
    indexed_target_uid: target, cursor_key: Buffer.alloc(32, 7)
  });
  assert.deepEqual(index.query({ target_uid: target, folder_path: "doc/a" }).items.map((item) => item.source_artifact_uid), [docsNested, docsA]);
  assert.throws(() => index.query({ target_uid: docsA }), /target-specific/);
});

test("target-specific pagination preserves cursor bindings and work exhaustion", () => {
  const { target, docsA, docsNested } = fixture();
  const prefix = `A-${"3".repeat(26)}`;
  const index = new FolderReverseReferenceIndex({
    snapshot_uid: snapshot, graph_root: graphRoot,
    artifacts: [artifact(target, "doc/target.md"), artifact(prefix, "aaa/outside.md"), artifact(docsA, "doc/a/one.md"), artifact(docsNested, "doc/a/two.md")],
    edges: [edge(`E-${"3".repeat(26)}`, docsNested, target), edge(`E-${"1".repeat(26)}`, prefix, target), edge(`E-${"2".repeat(26)}`, docsA, target)],
    indexed_target_uid: target, cursor_key: Buffer.alloc(32, 7)
  });
  const exhausted = index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 1 });
  assert.equal(exhausted.items.length, 0);
  assert.equal(exhausted.reason, "work_units");
  assert.equal(exhausted.counters.work_units, 1);
  const first = index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 2 });
  assert.equal(first.items.length, 1);
  assert.equal(first.reason, "limit");
  const second = index.query({ target_uid: target, folder_path: "doc/a", limit: 1, max_work_units: 2, cursor: first.next_cursor });
  assert.equal(second.complete, true);
  assert.equal(second.items.length, 1);
  assert.throws(() => index.query({ target_uid: target, folder_path: "doc", limit: 1, max_work_units: 2, cursor: first.next_cursor }), (error) => error.code === "SPK704");
});

test("lazy index neither caches misses nor freezes unresolved caller edges", () => {
  const target = `A-${"9".repeat(26)}`;
  const unresolved = edge(`E-${"8".repeat(26)}`, `SY-${"4".repeat(26)}`, target);
  const index = new FolderReverseReferenceIndex({
    snapshot_uid: snapshot, graph_root: graphRoot,
    artifacts: [artifact(target, "doc/target.md")], edges: [unresolved],
    cursor_key: Buffer.alloc(32, 7)
  });
  assert.equal(index.query({ target_uid: target }).items.length, 0);
  assert.equal(index.query({ target_uid: `A-${"7".repeat(26)}` }).items.length, 0);
  assert.equal(Object.isFrozen(unresolved), false);
  unresolved.edge_type = "depends_on";
  assert.equal(unresolved.edge_type, "depends_on");
});
