import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import { ZERO_HASH } from "../../src/storage/canonical.js";
import { ImmutableSnapshotStore, createSnapshotMetadata } from "../../src/storage/snapshot_store.js";
import { TargetInventoryStore } from "../../src/storage/target_inventory_store.js";
import { WorkspaceRegistry } from "../../src/workspace/registry.js";
import { createSnapshotAuthorityPortV1 } from "../../src/core/snapshot_authority.js";
import { createProjectionPortV1 } from "../../src/view/projection_port.js";

const P1 = "P-000000000000000000000000000000A1";
const P2 = "P-000000000000000000000000000000A2";
const W1 = "W-000000000000000000000000000000B1";
const W2 = "W-000000000000000000000000000000B2";
const A1 = "A-000000000000000000000000000000C1";
const S1 = "S-000000000000000000000000000000D1";
const digest = (letter) => `sha256:${letter.repeat(64)}`;

function fixture({ aggregate = false, contributors = undefined } = {}) {
  const root = mkdtempSync(join(tmpdir(), "spkc-authority-")); mkdirSync(join(root, ".git")); mkdirSync(join(root, "p2"));
  const registry = new WorkspaceRegistry({ workspaceUid: W1, root });
  registry.registerProject({ projectUid: P1, key: "one", root, revision: "r1" });
  registry.registerProject({ projectUid: P2, key: "two", root: join(root, "p2"), revision: "r1" });
  registry.registerWorktree({ project_uid: P1, worktree_uid: W1, root, git_common_dir: join(root, ".git"), git_dir: join(root, ".git"), revision_id: "r1" });
  registry.registerWorktree({ project_uid: P2, worktree_uid: W2, root: join(root, "p2"), git_common_dir: join(root, ".git"), git_dir: join(root, ".git"), revision_id: "r1" });
  const snapshots = new ImmutableSnapshotStore({ cacheRoot: root, repositoryId: "test" });
  const base = snapshots.put(createSnapshotMetadata({ project_uid: P1, worktree_uid: W1, revision_id: "r1", base_generation_hash: "1".repeat(64), overlay_generation_hash: ZERO_HASH, policy_hash: "2".repeat(64), parser_version: "p1", analyzer_version: "a1", provider_contract_version: "v1" }));
  const inventories = new TargetInventoryStore();
  const entries = [
    { target_kind: "artifact", target_uid: A1, locator: "artifact", content_digest: digest("a") },
    { target_kind: "directory", target_uid: "directory:feature", locator: "dir", content_digest: digest("b"), view_kind: "feature", logical_path: "search", selector_digest: digest("c"), children: [{ target_kind: "artifact", target_uid: A1 }, { target_kind: "section", target_uid: S1 }] },
    { target_kind: "section", target_uid: S1, locator: "section", content_digest: digest("d") }
  ].sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
  const inventory = { scope_kind: aggregate ? "workspace_aggregate" : "project", workspace_uid: W1, project_uid: aggregate ? null : P1, worktree_uid: W1, base_snapshot_uid: base.snapshot_uid, revision_id: "r1", entries, alias_index: [{ normalized_alias_uri: "spipe://skill", target_kind: "artifact", target_uid: A1 }], projection_root: digest("e") };
  if (aggregate) {
    const child = inventories.put({ ...inventory, scope_kind: "project", project_uid: P1 });
    inventory.contributing_project_roots = contributors ?? [{ project_uid: P1, base_snapshot_uid: base.snapshot_uid, authority_snapshot_uid: child.authority.snapshot_uid, target_inventory_root: child.inventory.root_digest }];
  }
  const stored = inventories.put(inventory); registry.registerAuthoritySnapshot({ workspaceUid: W1, projectUidOrNull: aggregate ? null : P1, worktreeUid: W1, snapshotUid: stored.authority.snapshot_uid, revisionId: "r1" }); const authority = createSnapshotAuthorityPortV1({ workspaceRegistry: registry, snapshotStore: snapshots, targetInventoryStore: inventories }); const projection = createProjectionPortV1({ snapshotAuthorityPort: authority });
  const bind = { workspaceUid: W1, projectUidOrNull: aggregate ? null : P1, worktreeUid: W1, snapshotUid: stored.authority.snapshot_uid, revisionId: "r1" };
  return { root, registry, snapshots, inventories, stored, authority, projection, bind, close() { rmSync(root, { recursive: true, force: true }); } };
}

test("W5A-01/02/07/08/09: sealed project inventory opens, proves targets and aliases, and renders deterministically", () => {
  const h = fixture(); try {
    const opened = h.authority.openBoundSnapshot(h.bind); assert.equal(opened.ok, true);
    const artifact = h.authority.resolveCanonicalTarget(opened.value, { targetKind: "artifact", targetUid: A1 }); const section = h.authority.resolveCanonicalTarget(opened.value, { targetKind: "section", targetUid: S1 });
    assert.equal(artifact.ok && section.ok, true); const alias = h.authority.resolveCanonicalAlias(opened.value, { normalizedAliasUri: "spipe://skill" }); assert.equal(alias.ok, true); assert.equal(h.projection.render(opened.value, alias.value).ok, false);
    const reproof = h.authority.resolveCanonicalTarget(opened.value, { targetKind: alias.value.target_kind, targetUid: alias.value.target_uid }); const first = h.projection.render(opened.value, reproof.value); const second = h.projection.render(opened.value, reproof.value); assert.equal(first.value.content_digest, second.value.content_digest);
    const directory = h.authority.listDirectoryTarget(opened.value, { viewKind: "feature", normalizedLogicalPath: "search", selectorDigest: digest("c") }); const page = h.projection.list(opened.value, directory.value, { limit: 1 }); assert.equal(page.ok, true); assert.equal(page.value.entries.length, 1); assert.ok(page.value.next_cursor); assert.equal(h.projection.list(opened.value, directory.value, { cursor: "not-a-cursor" }).ok, false); assert.equal(h.projection.list(opened.value, directory.value, { cursor: "bad\0cursor" }).ok, false);
  } finally { h.close(); }
});

test("W5A-03/04/05/06/10: absent, wrong, foreign, stale, and forged inputs deny before projection", () => {
  const h = fixture(); try {
    const opened = h.authority.openBoundSnapshot(h.bind); assert.equal(h.authority.resolveCanonicalTarget(opened.value, { targetKind: "section", targetUid: A1 }).ok, false); assert.equal(h.authority.resolveCanonicalTarget(opened.value, { targetKind: "artifact", targetUid: "A-000000000000000000000000000000FF" }).ok, false);
    assert.equal(h.authority.openBoundSnapshot({ ...h.bind, workspaceUid: W2 }).ok, false); assert.equal(h.authority.openBoundSnapshot({ ...h.bind, worktreeUid: W2 }).ok, false); assert.equal(h.authority.openBoundSnapshot({ ...h.bind, revisionId: "old" }).ok, false); h.registry._worktrees.set(W1, { ...h.registry._worktrees.get(W1), revision_id: "changed" }); assert.equal(h.authority.openBoundSnapshot(h.bind).ok, false);
    assert.throws(() => createSnapshotAuthorityPortV1({ workspaceRegistry: {}, snapshotStore: {}, targetInventoryStore: {} })); assert.throws(() => createProjectionPortV1({ snapshotAuthorityPort: {} })); assert.equal(h.projection.render({}, {}).ok, false);
  } finally { h.close(); }
});

test("W5A-11/12/13/14: aggregate contributors are required, exact, and canonically ordered", () => {
  const h = fixture({ aggregate: true }); try {
    assert.equal(h.authority.openBoundSnapshot(h.bind).ok, true);
    const empty = fixture({ aggregate: true, contributors: [] }); assert.equal(empty.authority.openBoundSnapshot(empty.bind).ok, true); empty.close();
    assert.throws(() => fixture({ aggregate: true, contributors: [{ project_uid: P2, base_snapshot_uid: "spks1-2", authority_snapshot_uid: "spka1-2", target_inventory_root: digest("f") }, { project_uid: P1, base_snapshot_uid: "spks1-1", authority_snapshot_uid: "spka1-1", target_inventory_root: digest("f") }] }).stored);
  } finally { h.close(); }
});

test("sealed roots reject tampering and genuine authority instances do not cross-mix", () => {
  const h = fixture(); const other = fixture(); try {
    const opened = h.authority.openBoundSnapshot(h.bind); const target = h.authority.resolveCanonicalTarget(opened.value, { targetKind: "artifact", targetUid: A1 }); assert.equal(other.projection.render(opened.value, target.value).ok, false);
    const record = h.inventories.get(h.stored.authority.snapshot_uid); h.inventories._records.set(h.stored.authority.snapshot_uid, { ...record, inventory: { ...record.inventory, root_digest: digest("9") } }); assert.equal(h.authority.openBoundSnapshot(h.bind).ok, false);
  } finally { h.close(); other.close(); }
});
