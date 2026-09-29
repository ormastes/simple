import assert from "node:assert/strict";
import test from "node:test";

import { contentHash } from "../../src/model/identity.js";
import { VIEW_KINDS } from "../../src/model/view.js";
import { SpipeUriError, parseSpipeUri, resolveVirtualResource } from "../../src/view/index.js";

const CONTEXT = Object.freeze({
  workspace_uid: "W-01K3R8G3N70ZMT43W6QJ7YHX4P",
  snapshot_id: "spks1-" + "a".repeat(64),
  revision_id: "f2a9ff0bdda",
  auth_scope_hash: contentHash("public-policy-v1"),
  resolution_port: Object.freeze({
    resolveWorkspace: ({ workspace, workspace_uid, revision_id, snapshot_id }) => ({ authorized: workspace === "simple" && workspace_uid === "W-01K3R8G3N70ZMT43W6QJ7YHX4P" && revision_id === "f2a9ff0bdda" && snapshot_id === "spks1-" + "a".repeat(64), workspace, workspace_uid, revision_id, snapshot_id }),
    resolveProject: ({ project, uid, kind, revision_id, snapshot_id }) => ({ authorized: project === "simple" && uid === "A-01K3R8G3N70ZMT43W6QJ7YHX4P" && kind === "artifact" && revision_id === "f2a9ff0bdda" && snapshot_id === "spks1-" + "a".repeat(64), project, canonical_uid: uid, kind, revision_id, snapshot_id }),
    resolveLegacySkill: ({ uri, revision_id, snapshot_id }) => ({ authorized: uri === "spipe://skill" && revision_id === "f2a9ff0bdda" && snapshot_id === "spks1-" + "a".repeat(64), uri, project: "simple", canonical_uid: "A-01K3R8G3N70ZMT43W6QJ7YHX4P", revision_id, snapshot_id })
  })
});

test("SPipe URIs resolve canonical resource families and stable aggregate identities", () => {
  const view = parseSpipeUri("spipe://workspace/simple/view/feature/search");
  assert.equal(view.type, "view");
  assert.equal(view.canonical_uri, "spipe://workspace/simple/view/feature/search");
  assert.deepEqual(view.parameters, {});
  const first = resolveVirtualResource(view.canonical_uri, CONTEXT);
  const second = resolveVirtualResource(view.canonical_uri, CONTEXT);
  assert.match(first.projection_uid, /^spkp1-[a-f0-9]{64}$/);
  assert.equal(first.projection_uid, second.projection_uid);
  assert.equal(first.logical_path, "feature/search");
  assert.equal(first.read_only, true);
  assert.notEqual(first.projection_uid, resolveVirtualResource(view.canonical_uri, { ...CONTEXT, page_start_key: "next" }).projection_uid);
  assert.notEqual(first.projection_uid, resolveVirtualResource(view.canonical_uri, { ...CONTEXT, auth_scope_hash: contentHash("private-alice") }).projection_uid);
});

test("project UID resources retain canonical identity while legacy skill remains read-only", () => {
  const artifact = resolveVirtualResource("spipe://project/simple/artifact/A-01K3R8G3N70ZMT43W6QJ7YHX4P", CONTEXT);
  assert.equal(artifact.canonical_uid, "A-01K3R8G3N70ZMT43W6QJ7YHX4P");
  assert.equal(artifact.type, "artifact");
  assert.deepEqual(resolveVirtualResource("spipe://skill", CONTEXT), {
    type: "legacy_skill", canonical_uri: "spipe://skill", canonical_uid: "A-01K3R8G3N70ZMT43W6QJ7YHX4P", project: "simple", revision_id: "f2a9ff0bdda", snapshot_id: "spks1-" + "a".repeat(64), read_only: true
  });
});

test("the canonical trailing-slash workspace directory spelling is accepted", () => {
  const root = resolveVirtualResource("spipe://workspace/simple/", CONTEXT);
  assert.equal(root.type, "workspace_directory");
  assert.equal(root.canonical_uri, "spipe://workspace/simple/");
  assert.match(root.projection_uid, /^spkp1-[a-f0-9]{64}$/);
});

test("URI parser rejects traversal, double decode, Windows and ambiguous query hazards", () => {
  for (const value of [
    "spipe://workspace/simple/view/feature/..",
    "spipe://workspace/simple/view/feature/%2e%2e",
    "spipe://workspace/simple/view/feature/%252fetc",
    "spipe://workspace/simple/view/feature/a%5cb",
    "spipe://workspace/C:/view/feature/search",
    "spipe://workspace/%5c%5cserver/view/feature/search",
    "spipe://workspace/%5c%3f%5cC%3a/view/feature/search",
    "spipe://workspace/simple/view/feature/alternate%3Adata",
    "spipe://workspace/simple/view/feature/search.",
    "spipe://workspace/simple/view/feature/search%20",
    "spipe://workspace/simple/view/feature/%E0%A4",
    "spipe://workspace/simple/project/artifact/not-a-uid",
    "spipe://project/simple/artifact/not-a-uid",
    "spipe://project/simple/section/not-a-uid",
    "spipe://workspace/simple/view/feature/search?x=1&x=2",
    "spipe://workspace/simple/view/feature/search#section",
    "spipe://workspace/simple/view/feature/search?x=%252e%252e"
  ]) {
    assert.throws(() => parseSpipeUri(value), (error) => error instanceof SpipeUriError && error.code === "SPK101", value);
  }
});

test("URI resolver rejects forged targets and parser enforces UID, byte, device and UTF-8 limits", () => {
  assert.throws(() => resolveVirtualResource({ type: "artifact", uid: "A-01K3R8G3N70ZMT43W6QJ7YHX4P", canonical_uri: "spipe://project/forged/artifact/A-01K3R8G3N70ZMT43W6QJ7YHX4P" }, CONTEXT), SpipeUriError);
  for (const value of [
    "spipe://workspace/simple/trace/not-a-uid",
    "spipe://workspace/CON/view/feature/search",
    "spipe://workspace/simple/view/feature/NUL.txt",
    `spipe://workspace/simple/view/feature/search?x=${"a".repeat(4097)}`,
    `spipe://workspace/${"a".repeat(8192)}`,
    "spipe://workspace/\ud800/view/feature/search"
  ]) assert.throws(() => parseSpipeUri(value), (error) => error instanceof SpipeUriError && error.code === "SPK101", value.slice(0, 80));
  assert.throws(() => parseSpipeUri("spipe://workspace/simple/view/feature/search?tag=alpha"), SpipeUriError);
});

test("resolution requires workspace/project/revision receipts and rejects cache namespace confusion", () => {
  assert.throws(() => resolveVirtualResource("spipe://workspace/attacker/view/feature/search", CONTEXT), SpipeUriError);
  assert.throws(() => resolveVirtualResource("spipe://project/attacker/artifact/A-01K3R8G3N70ZMT43W6QJ7YHX4P", CONTEXT), SpipeUriError);
  assert.throws(() => resolveVirtualResource("spipe://project/simple/section/S-01K3R8G3N70ZMT43W6QJ7YHX4P", CONTEXT), SpipeUriError);
  assert.throws(() => resolveVirtualResource("spipe://workspace/simple/view/feature/search", { ...CONTEXT, revision_id: "wrong" }), SpipeUriError);
  assert.throws(() => resolveVirtualResource("spipe://workspace/simple/view/feature/search?unknown=value", CONTEXT), SpipeUriError);
});

test("all virtual resource families and view kinds have a typed successful resolution", () => {
  for (const kind of VIEW_KINDS) {
    const result = resolveVirtualResource(`spipe://workspace/simple/view/${kind}/root`, CONTEXT);
    assert.equal(result.view_kind, kind);
    assert.match(result.projection_uid, /^spkp1-[a-f0-9]{64}$/);
  }
  assert.match(resolveVirtualResource("spipe://workspace/simple/trace/A-01K3R8G3N70ZMT43W6QJ7YHX4P", CONTEXT).projection_uid, /^spkp1-/);
  assert.match(resolveVirtualResource("spipe://workspace/simple/diagnostics", CONTEXT).projection_uid, /^spkp1-/);
});

test("authorization receipts are closed, snapshot-bound, kind-bound and getter-free", () => {
  const workspaceUri = "spipe://workspace/simple/view/feature/search";
  const withPort = (resolution_port) => ({ ...CONTEXT, resolution_port });
  assert.throws(() => resolveVirtualResource(workspaceUri, withPort({ ...CONTEXT.resolution_port, resolveWorkspace: ({ workspace, workspace_uid, revision_id, snapshot_id }) => ({ authorized: true, workspace, workspace_uid, revision_id, snapshot_id, extra: true }) })), SpipeUriError);
  const getterReceipt = { authorized: true, workspace: "simple", workspace_uid: CONTEXT.workspace_uid, revision_id: CONTEXT.revision_id, snapshot_id: CONTEXT.snapshot_id };
  Object.defineProperty(getterReceipt, "workspace", { enumerable: true, get: () => "simple" });
  assert.throws(() => resolveVirtualResource(workspaceUri, withPort({ ...CONTEXT.resolution_port, resolveWorkspace: () => getterReceipt })), SpipeUriError);
  assert.throws(() => resolveVirtualResource(workspaceUri, { ...CONTEXT, snapshot_id: "spks1-" + "b".repeat(64) }), SpipeUriError);
  assert.throws(() => resolveVirtualResource("spipe://project/simple/artifact/A-01K3R8G3N70ZMT43W6QJ7YHX4P", withPort({ ...CONTEXT.resolution_port, resolveProject: ({ project, uid, kind, revision_id, snapshot_id }) => ({ authorized: true, project, canonical_uid: uid, kind: "section", revision_id, snapshot_id }) })), SpipeUriError);
});

test("UID kinds are exact and NFC/NFD inputs canonicalize without case folding", () => {
  for (const value of [
    "spipe://project/simple/artifact/S-01K3R8G3N70ZMT43W6QJ7YHX4P",
    "spipe://project/simple/section/A-01K3R8G3N70ZMT43W6QJ7YHX4P",
    "spipe://project/simple/artifact/P-P-01K3R8G3N70ZMT43W6QJ7YHX4P-" + "a".repeat(64)
  ]) assert.throws(() => parseSpipeUri(value), SpipeUriError);
  assert.equal(parseSpipeUri("spipe://workspace/café/view/feature/search").canonical_uri,
    parseSpipeUri("spipe://workspace/cafe%CC%81/view/feature/search").canonical_uri);
});

test("URI comparison is NFC canonical and preserves case-sensitive identity", () => {
  const normalized = parseSpipeUri("spipe://workspace/cafe%CC%81/view/feature/search");
  assert.equal(normalized.workspace, "café");
  assert.equal(normalized.canonical_uri, "spipe://workspace/caf%C3%A9/view/feature/search");
  assert.notEqual(parseSpipeUri("spipe://workspace/Simple/view/feature/search").workspace,
    parseSpipeUri("spipe://workspace/simple/view/feature/search").workspace);
});
