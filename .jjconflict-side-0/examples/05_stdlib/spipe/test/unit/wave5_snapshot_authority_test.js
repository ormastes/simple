import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { generateKeyPairSync } from "node:crypto";

import { compileKnowledgeDelta, compileKnowledgeInventory } from "../../src/core/knowledge_compiler.js";
import { ZERO_HASH, canonicalJson } from "../../src/storage/canonical.js";
import { ImmutableSnapshotStore } from "../../src/storage/snapshot_store.js";
import { AuthorityManifestStoreV1, AuthorityPublisherV1, SnapshotAuthorityPortV1 } from "../../src/view/authority.js";
import { CursorAuthorityV1, ProjectionPortV1 } from "../../src/view/projection.js";
import { WorkspaceRegistry } from "../../src/workspace/registry.js";

const P = "P-000000000000000000000000000000AA";
const W = "W-000000000000000000000000000000BB";
const X = "W-000000000000000000000000000000BC";
const WS = "W-000000000000000000000000000000CC";
const context = { project_uid: P, worktree_uid: W, revision_id: "rev-wave5a", overlay_generation_hash: ZERO_HASH, policy_hash: "4".repeat(64) };
const marked = `<!-- spipe:artifact uid=A-00000000000000000000000000000001 key=design.search.core -->\n# Search Core\n\n## Stable identity\n<!-- spipe:section uid=S-00000000000000000000000000000001 key=design.search.identity -->\nBody.\n`;
function root() { return mkdtempSync(join(tmpdir(), "spipe-wave5a-")); }
function setup(inventory = null) {
  const cache = root(); const snapshots = new ImmutableSnapshotStore({ cacheRoot: cache, repositoryId: "test" });
  const manifests = new AuthorityManifestStoreV1({ root: join(cache, "authority") });
  const registry = new WorkspaceRegistry({ workspaceUid: WS, root: cache });
  registry.registerProject({ uid: P, key: "test", root: cache, revision: context.revision_id });
  registry.registerWorktree({ worktree_uid: W, project_uid: P, root: cache, revision_id: context.revision_id });
  const publisher = new AuthorityPublisherV1({ store: manifests, snapshotStore: snapshots, registry });
  const compiled = inventory ?? compileKnowledgeInventory({ ...context, inputs: [{ path: "doc/search.md", content: marked }] });
  const published = publisher.publishProject({ workspaceUid: WS, inventory: compiled, aliases: { "spipe://skill": { targetKind: "artifact", targetUid: "A-00000000000000000000000000000001" } } });
  const authority = new SnapshotAuthorityPortV1({ store: manifests, snapshotStore: snapshots, registry }); const keys = generateKeyPairSync("ed25519"); const cursorAuthority = new CursorAuthorityV1({ issuerKeyId: "test", privateKey: keys.privateKey, publicKeys: { test: keys.publicKey }, now: () => 1_000 }); const projection = new ProjectionPortV1({ authority, cursorAuthority });
  const binding = { workspaceUid: WS, projectUidOrNull: P, worktreeUid: W, snapshotUid: published.authority.snapshotUid, revisionId: context.revision_id };
  return { cache, snapshots, manifests, registry, publisher, compiled, published, authority, cursorAuthority, projection, binding };
}
function open(subject) { const result = subject.authority.openBoundSnapshot(subject.binding); assert.equal(result.ok, true); return result.value; }
function target(subject, view, kind = "artifact", uid = "A-00000000000000000000000000000001") { const result = subject.authority.resolveCanonicalTarget(view, { targetKind: kind, targetUid: uid }); assert.equal(result.ok, true); return result.value; }

test("W5A-01/02 opens only exact sealed snapshot and proves artifact/section before render", () => {
  const subject = setup(); try { const view = open(subject); assert.equal(view.binding.snapshotUid, subject.binding.snapshotUid); assert.equal(typeof view.manifestDigest, "string");
    assert.match(subject.projection.render(view, target(subject, view)).value.bytes.toString(), /Search Core/);
    assert.match(subject.projection.render(view, target(subject, view, "section", "S-00000000000000000000000000000001")).value.bytes.toString(), /Body/);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});

test("W5A-03/04/05/06/10 deny wrong target, foreign tuple, stale revision, duck objects without projection", () => {
  const subject = setup(); try { const view = open(subject);
    assert.equal(subject.authority.resolveCanonicalTarget(view, { targetKind: "artifact", targetUid: "A-missing" }).ok, false);
    assert.equal(subject.authority.resolveCanonicalTarget(view, { targetKind: "section", targetUid: "A-00000000000000000000000000000001" }).ok, false);
    assert.equal(subject.authority.openBoundSnapshot({ ...subject.binding, worktreeUid: X }).ok, false);
    assert.equal(subject.authority.openBoundSnapshot({ ...subject.binding, revisionId: "old" }).ok, false);
    assert.equal(subject.projection.render({}, {}).ok, false);
    assert.equal(subject.authority.resolveCanonicalAlias(view, { normalizedAliasUri: "../secret" }).ok, false);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});

test("W5A-07 aliases are candidates only and require a separate sealed target proof", () => {
  const subject = setup(); try { const view = open(subject); const candidate = subject.authority.resolveCanonicalAlias(view, { normalizedAliasUri: "spipe://skill" }); assert.equal(candidate.ok, true);
    assert.equal(subject.projection.render(view, candidate.value).ok, false);
    assert.equal(subject.authority.resolveCanonicalTarget(view, candidate.value).ok, true);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});

test("W5A-08 clean and incremental compiler publication have byte-identical sealed output", () => {
  const first = compileKnowledgeInventory({ ...context, inputs: [{ path: "doc/search.md", content: marked }] });
  const delta = compileKnowledgeDelta(first, [{ operation: "upsert", path: "doc/temp.md", content: "# Temp\n" }]);
  const incremental = compileKnowledgeDelta(delta.inventory, [{ operation: "delete", path: "doc/temp.md" }]).inventory;
  const clean = compileKnowledgeInventory({ ...context, inputs: [{ path: "doc/search.md", content: marked }] });
  const one = setup(incremental), two = setup(clean); try { assert.equal(canonicalJson(one.published.inventory), canonicalJson(two.published.inventory)); assert.equal(canonicalJson(one.published.authority), canonicalJson(two.published.authority)); assert.equal(one.projection.render(open(one), target(one, open(one))).value.bytes.toString(), two.projection.render(open(two), target(two, open(two))).value.bytes.toString());
  } finally { rmSync(one.cache, { recursive: true, force: true }); rmSync(two.cache, { recursive: true, force: true }); }
});

test("W5A-09 list is deterministic, bounded, and cursor-bound", () => {
  const subject = setup(); try { const view = open(subject); const selectorDigest = subject.published.inventory.directories[0].selectorDigest; const directory = subject.authority.listDirectoryTarget(view, { viewKind: "lifecycle", normalizedLogicalPath: "lifecycle", selectorDigest }); assert.equal(directory.ok, true);
    const first = subject.projection.list(view, directory.value, { limit: 1 }); assert.equal(first.ok, true); assert.equal(first.value.entries.length, 1); assert.ok(first.value.cursor);
    const second = subject.projection.list(view, directory.value, { limit: 1, cursor: first.value.cursor }); assert.equal(second.ok, true); assert.notEqual(second.value.entries[0]?.sortKey, first.value.entries[0]?.sortKey);
    assert.equal(subject.projection.list(view, directory.value, { limit: 2, cursor: first.value.cursor }).ok, false);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});

test("sealed store detects tampering and survives restart selection", () => {
  const subject = setup(); try { const path = subject.manifests.pathFor(subject.binding.snapshotUid); const fresh = new AuthorityManifestStoreV1({ root: join(subject.cache, "authority") }); const port = new SnapshotAuthorityPortV1({ store: fresh, snapshotStore: subject.snapshots, registry: subject.registry }); assert.equal(port.openBoundSnapshot(subject.binding).ok, true);
    const tampered = JSON.parse(readFileSync(path)); tampered.inventory.entries[0].title = "leak"; writeFileSync(path, `${JSON.stringify(tampered)}\n`); assert.equal(port.openBoundSnapshot(subject.binding).ok, false);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});

test("W5A-11/12/13/14 aggregate contributors are exact, complete, and ordered", () => {
  const subject = setup(); try { const child = subject.published; const contributors = [{ projectUid: P, baseSnapshotUid: child.inventory.baseSnapshotUid, authoritySnapshotUid: child.authority.snapshotUid, targetInventoryRoot: child.inventory.rootDigest }];
    const aggregate = subject.publisher.publishAggregate({ workspaceUid: WS, worktreeUid: W, revisionId: context.revision_id, contributors, entries: [{ targetKind: "aggregate", targetUid: "AG-root", logicalPath: "aggregate/root", directoryPath: "root", title: "Root", content: "aggregate", sortKey: "aggregate:root" }] });
    const binding = { workspaceUid: WS, projectUidOrNull: null, worktreeUid: W, snapshotUid: aggregate.authority.snapshotUid, revisionId: context.revision_id }; assert.equal(subject.authority.openBoundSnapshot(binding).ok, true);
    assert.throws(() => subject.publisher.publishAggregate({ workspaceUid: WS, worktreeUid: W, revisionId: context.revision_id, contributors: [], entries: [] }), /durable workspace selection/);
    assert.throws(() => subject.publisher.publishAggregate({ workspaceUid: WS, worktreeUid: W, revisionId: context.revision_id, contributors: [...contributors, { ...contributors[0], projectUid: "P-foreign" }], entries: [] }), /durable workspace selection/);
    assert.throws(() => subject.publisher.publishAggregate({ workspaceUid: WS, worktreeUid: W, revisionId: context.revision_id, contributors: [{ ...contributors[0], targetInventoryRoot: "wrong" }], entries: [] }), /aggregate contributor root/);
  } finally { rmSync(subject.cache, { recursive: true, force: true }); }
});
