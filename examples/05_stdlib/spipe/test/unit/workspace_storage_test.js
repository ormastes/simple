import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import { canonicalJson, ZERO_HASH } from "../../src/storage/canonical.js";
import { ContentAddressedObjectStore } from "../../src/storage/object_store.js";
import { WorktreeOverlayStore } from "../../src/storage/overlay_store.js";
import { ImmutableSnapshotStore, createSnapshotMetadata, computeSnapshotId } from "../../src/storage/snapshot_store.js";
import { createProjectRelation } from "../../src/workspace/linked_project.js";
import { normalizeRelativePath } from "../../src/workspace/paths.js";
import { WorkspaceRegistry } from "../../src/workspace/registry.js";
import { createWorktreeRecord, deriveWorktreeUid } from "../../src/workspace/worktree.js";

function tempRoot() {
  return mkdtempSync(join(tmpdir(), "spipe-workspace-storage-"));
}

function snapshotInput(overrides = {}) {
  return {
    project_uid: "P-project",
    worktree_uid: "WT-one",
    revision_id: "git:abc123",
    base_generation_hash: "1".repeat(64),
    overlay_generation_hash: ZERO_HASH,
    schema_version: 1,
    parser_version: "markdown@1",
    analyzer_version: "analyzer@1",
    provider_contract_version: "provider@1",
    policy_hash: "2".repeat(64),
    ...overrides
  };
}

test("project relations keep semantic dependency separate from physical linkage", () => {
  const relation = createProjectRelation({
    from_project_uid: "P-simple",
    to_project_uid: "P-spipe",
    semantic: "extends",
    physical: "gitlink",
    revision: "abc123",
    version_relation: "pinned",
    mount: ".spipe/spipe_project",
    trust: "trusted"
  });
  assert.equal(relation.semantic, "extends");
  assert.equal(relation.physical, "gitlink");
  assert.equal(relation.trust, "trusted");
  assert.notEqual(relation.semantic, relation.physical);
});

test("registry round-trips projects, explicit relations, and worktree identity", () => {
  const root = tempRoot();
  try {
    const registry = new WorkspaceRegistry({ root });
    const spipe = registry.registerProject({ key: "spipe", root });
    const simple = registry.registerProject({ key: "simple", root: join(root, "simple") });
    registry.registerRelation({
      from_project_uid: simple.project_uid,
      to_project_uid: spipe.project_uid,
      semantic: "extends",
      physical: "path",
      mount: ".spipe",
      revision: "git:abc",
      trust: "trusted"
    });
    const worktree = registry.registerWorktree({
      project_uid: simple.project_uid,
      root,
      git_common_dir: join(root, ".git-common"),
      git_dir: join(root, ".git-worktree"),
      revision_id: "git:abc"
    });
    assert.match(worktree.worktree_uid, /^WT-[a-f0-9]{64}$/);
    assert.equal(registry.relationsFrom(simple.project_uid).length, 1);
    assert.equal(registry.worktreesFor(simple.project_uid)[0].worktree_uid, worktree.worktree_uid);
    const restored = WorkspaceRegistry.fromRecord(JSON.parse(registry.toJSON()));
    assert.equal(restored.toJSON(), registry.toJSON());
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("worktree UID uses Git common-dir and Git-dir, not only checkout path", () => {
  const first = deriveWorktreeUid({ projectUid: "P-x", gitCommonDir: "/repo/.git", gitDir: "/repo/.git/worktrees/a" });
  const second = deriveWorktreeUid({ projectUid: "P-x", gitCommonDir: "/repo/.git", gitDir: "/repo/.git/worktrees/b" });
  assert.notEqual(first, second);
  assert.equal(first, deriveWorktreeUid({ projectUid: "P-x", gitCommonDir: "/repo/.git", gitDir: "/repo/.git/worktrees/a" }));
  const record = createWorktreeRecord({ project_uid: "P-x", root: "/repo", worktree_uid: "WT-explicit" });
  assert.equal(record.cache_namespace, "WT-explicit");
});

test("canonical relative paths reject traversal and alternate separators", () => {
  assert.equal(normalizeRelativePath("doc/05_design/search.md"), "doc/05_design/search.md");
  assert.throws(() => normalizeRelativePath("../outside"), /dot and dot-dot/);
  assert.throws(() => normalizeRelativePath("doc\\outside"), /backslash/);
  assert.throws(() => normalizeRelativePath("/absolute"), /absolute/);
});

test("content-addressed object store deduplicates and verifies immutable bytes", () => {
  const root = tempRoot();
  try {
    const store = new ContentAddressedObjectStore({ root });
    const first = store.putText("same bytes");
    const second = store.putText("same bytes");
    assert.equal(first.hash, second.hash);
    assert.equal(second.existed, true);
    assert.equal(store.get(first.hash).toString(), "same bytes");
    assert.equal(store.verify(first.hash), true);
    assert.equal(store.stat(first.hash).size, 10);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("dirty overlays are isolated by worktree and reload from their own manifest", () => {
  const root = tempRoot();
  try {
    const one = new WorktreeOverlayStore({ cacheRoot: root, worktreeUid: "WT-one" });
    const two = new WorktreeOverlayStore({ cacheRoot: root, worktreeUid: "WT-two" });
    assert.equal(one.snapshot().overlay_generation_hash, ZERO_HASH);
    one.set("doc/state.md", "one");
    two.set("doc/state.md", "two");
    assert.equal(one.read("doc/state.md").toString(), "one");
    assert.equal(two.read("doc/state.md").toString(), "two");
    assert.notEqual(one.snapshot().overlay_generation_hash, two.snapshot().overlay_generation_hash);
    const reloaded = new WorktreeOverlayStore({ cacheRoot: root, worktreeUid: "WT-one" });
    assert.equal(reloaded.read("doc/state.md").toString(), "one");
    two.delete("doc/state.md");
    assert.equal(two.read("doc/state.md"), null);
    assert.equal(one.read("doc/state.md").toString(), "one");
    assert.notEqual(readFileSync(join(root, "worktrees", "WT-one", "current.sdn"), "utf8"), readFileSync(join(root, "worktrees", "WT-two", "current.sdn"), "utf8"));
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("snapshot identity is deterministic, worktree-bound, and immutable", () => {
  const first = createSnapshotMetadata(snapshotInput({ base_segments: ["sha256:" + "b".repeat(64), "sha256:" + "a".repeat(64)] }));
  const reordered = createSnapshotMetadata(snapshotInput({ base_segments: ["sha256:" + "a".repeat(64), "sha256:" + "b".repeat(64)] }));
  const otherWorktree = createSnapshotMetadata(snapshotInput({ worktree_uid: "WT-two" }));
  assert.equal(first.snapshot_uid, reordered.snapshot_uid);
  assert.match(first.snapshot_uid, /^spks1-[a-f0-9]{64}$/);
  assert.notEqual(first.snapshot_uid, otherWorktree.snapshot_uid);
  assert.equal(computeSnapshotId(snapshotInput()), createSnapshotMetadata(snapshotInput()).snapshot_uid);
  const root = tempRoot();
  try {
    const store = new ImmutableSnapshotStore({ cacheRoot: root, repositoryId: "repo" });
    const saved = store.put(first);
    assert.equal(store.read(saved.snapshot_uid).snapshot_uid, saved.snapshot_uid);
    assert.throws(() => store.put({ ...first, policy_hash: "3".repeat(64), snapshot_uid: first.snapshot_uid }), /does not match/);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("canonical metadata serialization is stable across key insertion order", () => {
  assert.equal(canonicalJson({ z: 1, a: { d: 4, c: 3 } }), canonicalJson({ a: { c: 3, d: 4 }, z: 1 }));
});
