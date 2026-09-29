import assert from "node:assert/strict";
import test from "node:test";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { WorkspaceRegistry } from "../../src/workspace/registry.js";
import { ImmutableSnapshotStore } from "../../src/storage/snapshot_store.js";
import { AuthorityPublicationJournalV1 } from "../../src/storage/authority_publication_journal.js";
import { KnowledgeCompilerCommitPublisherV1 } from "../../src/core/knowledge_compiler_commit_publisher.js";
import { canonicalJson, contentHash } from "../../src/storage/canonical.js";

const ID = "01K3R8G3N70ZMT43W6QJ7YHX4P";
const W = `W-${ID}`, WT = W, P1 = `P-${ID}`, P2 = "P-01K3R8G3N70ZMT43W6QJ7YHX4Q";
function root(dir, faultInjector = null) {
  const registry = new WorkspaceRegistry({ workspaceUid: W, root: dir });
  registry.registerProject({ projectUid: P1, key: "one", root: dir, revision: "rev-1" });
  registry.registerProject({ projectUid: P2, key: "two", root: dir, revision: "rev-1" });
  registry.registerWorktree({ worktree_uid: WT, project_uid: P1, root: dir, revision_id: "rev-1" });
  const snapshots = new ImmutableSnapshotStore({ cacheRoot: dir, repositoryId: "commit-test" });
  const journal = new AuthorityPublicationJournalV1({ cacheRoot: dir, repositoryId: "commit-test", worktreeUid: WT, faultInjector });
  return { registry, journal, publisher: new KnowledgeCompilerCommitPublisherV1({ registry, snapshotStore: snapshots, journal }) };
}
function nextInput(registry, prior) {
  return { ...input(registry, [
    { project_uid: P1, path: "doc/one.md", content: "# One revised\n\n## A\n" },
    { project_uid: P2, path: "doc/two.md", content: "# Two\n\n## B\n" }
  ]), commitId: "commit-2", expectedBaseSnapshotUidOrNull: prior.base_snapshot_uid, expectedPublicationUidOrNull: prior.publication_uid };
}
function input(registry, changes = null) {
  return { commitId: "commit-1", workspaceUid: W, projectUidOrNull: P1, worktreeUid: WT, revisionId: "rev-1",
    expectedRegistryRevisionId: contentHash(canonicalJson(registry.toRecord())), expectedBaseSnapshotUidOrNull: null, expectedPublicationUidOrNull: null,
    inputDeltas: changes ?? [
      { project_uid: P1, path: "doc/one.md", content: "# One\n\n## A\n" },
      { project_uid: P2, path: "doc/two.md", content: "# Two\n\n## B\n" }
    ] };
}
test("W5A-25/26 publishes one branded all-and-only dual-snapshot inventory and replays exactly", () => {
  const dir = mkdtempSync(join(tmpdir(), "spkc-publisher-"));
  try {
    const state = root(dir), request = input(state.registry);
    const first = state.publisher.commit(request);
    assert.equal(first.status, "published"); assert.equal(first.build.projects.length, 2);
    assert.deepEqual(first.build.aggregate.contributors.map((x) => x.project_uid), [P1, P2].sort());
    assert.equal(state.journal.current().publication_uid, first.record.publication_uid);
    assert.equal(JSON.parse(state.journal.readImmutableObjectV1(first.record.inventory_manifest_digest)).schema, "spipe-target-inventory-v1");
    assert.equal(JSON.parse(state.journal.readImmutableObjectV1(first.record.authority_manifest_digest)).schema, "spipe-authority-manifest-v1");
    assert.equal(state.publisher.commit(request).status, "replayed");
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
test("W5A-27/29 rejects incomplete contributors (no untrusted carry-forward) and stale or altered replay before publication", () => {
  const dir = mkdtempSync(join(tmpdir(), "spkc-publisher-"));
  try {
    const state = root(dir);
    assert.throws(() => state.publisher.commit(input(state.registry, [{ project_uid: P1, path: "x.md", content: "# X" }])), /all-and-only/);
    const request = input(state.registry), first = state.publisher.commit(request);
    assert.throws(() => state.publisher.commit({ ...request, revisionId: "rev-2" }), /stale|altered|tuple/);
    assert.equal(state.journal.current().publication_uid, first.record.publication_uid);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
test("W5A-28/30 journal exposes only complete current records and rejects substitution", () => {
  const dir = mkdtempSync(join(tmpdir(), "spkc-publisher-"));
  try {
    const state = root(dir), first = state.publisher.commit(input(state.registry));
    assert.deepEqual(state.journal.recoverAuthorityPublicationV1().record, first.record);
    assert.throws(() => state.journal.publishAuthorityPublicationV1(first.record.publication_uid, { ...first.record, revision_id: "substituted" }), /collision/);
    assert.deepEqual(state.journal.current(), first.record);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
test("W5A-28 fault schedule: every staging/durability/CAS/ack boundary exposes only complete old or new records", () => {
  const boundaries = [
    "object-stage", "object-write", "object-file-fsync", "object-rename", "object-parent-fsync",
    "publication-record-stage", "publication-record-write", "publication-record-file-fsync", "publication-record-rename", "publication-record-parent-fsync",
    "current-pointer-cas", "current-pointer-stage", "current-pointer-write", "current-pointer-file-fsync", "current-pointer-rename", "current-pointer-parent-fsync", "ack"
  ];
  for (const boundary of boundaries) {
    const dir = mkdtempSync(join(tmpdir(), "spkc-publisher-fault-"));
    try {
      const initial = root(dir), old = initial.publisher.commit(input(initial.registry)).record;
      const reads = [];
      const crashing = root(dir, (at) => {
        const reader = new AuthorityPublicationJournalV1({ cacheRoot: dir, repositoryId: "commit-test", worktreeUid: WT });
        const observed = reader.recoverAuthorityPublicationV1().record;
        if (observed !== null) reads.push(observed.publication_uid);
        if (at === boundary) throw new Error(`injected:${boundary}`);
      });
      const request = nextInput(crashing.registry, old);
      assert.throws(() => crashing.publisher.commit(request), new RegExp(`injected:${boundary}`));
      const restarted = root(dir);
      const afterCrash = restarted.journal.recoverAuthorityPublicationV1().record;
      // Before the pointer boundary recovery has the old head; after CAS/ack it
      // has the new complete head.  No staged record is ever observable.
      assert.ok(afterCrash === null || afterCrash.publication_uid === old.publication_uid || afterCrash.commit_id === "commit-2");
      const result = restarted.publisher.commit(nextInput(restarted.registry, old));
      const final = restarted.journal.recoverAuthorityPublicationV1().record;
      assert.ok(["published", "replayed"].includes(result.status));
      assert.equal(final.commit_id, "commit-2");
      assert.ok(reads.every((uid) => uid === old.publication_uid || uid === final.publication_uid));
    } finally { rmSync(dir, { recursive: true, force: true }); }
  }
});
