import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import { ZERO_HASH, canonicalJson, sha256Hex } from "../../src/storage/canonical.js";
import { ImmutableSnapshotStore } from "../../src/storage/snapshot_store.js";
import { WorkspaceRegistry } from "../../src/workspace/registry.js";
import { createSealedSnapshotAuthorityV1 } from "../../src/core/snapshot_authority.js";

const P = "P-00000000000000000000000000";
const W = "W-00000000000000000000000000";
const hash = (value) => `sha256:${sha256Hex(canonicalJson(value))}`;

function fixture() {
  const root = mkdtempSync(join(tmpdir(), "spkc-authority-"));
  const registry = new WorkspaceRegistry({ workspaceUid: "W-00000000000000000000000001", root });
  registry.registerProject({ project_uid: P, key: "test", root, revision: "r1" });
  registry.registerWorktree({ worktree_uid: W, project_uid: P, root, revision_id: "r1" });
  const store = new ImmutableSnapshotStore({ cacheRoot: root });
  const snapshot = store.put({ project_uid: P, worktree_uid: W, revision_id: "r1", base_generation_hash: "1".repeat(64), overlay_generation_hash: ZERO_HASH, policy_hash: "2".repeat(64), parser_version: "p1", analyzer_version: "a1", provider_contract_version: "c1" });
  const authority = createSealedSnapshotAuthorityV1({ registry, snapshotStore: store, authorityRoot: join(root, "authority") });
  return { root, registry, store, snapshot, authority };
}

test("sealed authority accepts only a branded commit permit and revalidates exact live binding", () => {
  const f = fixture();
  try {
    const directory = { targetUid: "A-00000000000000000000000000", orderingVersion: "spipe-directory-order-v1", maxPageLimit: 100, tokenBudget: 6000, children: [] };
    const inventory = { schema: 1, authoritySnapshotUid: "as-1", baseSnapshotUid: f.snapshot.snapshot_uid, registryRevisionId: f.registry.registryRevisionId(), scope: "project", targets: [{ targetUid: directory.targetUid, kind: "directory", contentDigest: `sha256:${"3".repeat(64)}` }], directories: [directory], contributingProjectRoots: [] };
    const manifest = { schema: 1, workspaceUid: f.registry.workspace_uid, projectUidOrNull: P, worktreeUid: W, baseSnapshotUid: f.snapshot.snapshot_uid, authoritySnapshotUid: "as-1", revisionId: "r1", registryRevisionId: f.registry.registryRevisionId(), targetInventoryRoot: hash(inventory), inventoryDigest: hash(inventory), contributingProjectRoots: [] };
    assert.throws(() => f.authority.publishAuthorityInventoryV1({ permit: {}, build: { manifest, inventory } }), /permit/);
    const permit = f.authority.mintCommitPublisherPermitV1();
    f.authority.publishAuthorityInventoryV1({ permit, build: { manifest, inventory } });
    const view = f.authority.openPublishedAuthorityInventoryV1({ authoritySnapshotUid: "as-1", workspaceUid: f.registry.workspace_uid, worktreeUid: W, baseSnapshotUid: f.snapshot.snapshot_uid, registryRevisionId: f.registry.registryRevisionId() });
    assert.equal(f.authority.isSnapshotAuthorityViewV1(view), true);
    assert.equal(f.authority.deriveContinuationDomainV1(manifest, directory), f.authority.deriveContinuationDomainV1(manifest, directory));
    assert.throws(() => f.authority.openPublishedAuthorityInventoryV1({ authoritySnapshotUid: "as-1", workspaceUid: f.registry.workspace_uid, worktreeUid: W, baseSnapshotUid: f.snapshot.snapshot_uid, registryRevisionId: "sha256:" + "0".repeat(64) }), /binding/);
  } finally { rmSync(f.root, { recursive: true, force: true }); }
});
