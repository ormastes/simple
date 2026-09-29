import assert from "node:assert/strict";
import test from "node:test";

import { deepFreeze } from "../../src/model/identity.js";
import { hashCanonical } from "../../src/index/document.js";
import { SNAPSHOT_LEXICAL_SEARCH_CONTRACT, SnapshotLexicalSearchV1 } from "../../src/search/snapshot_lexical.js";

const W = "W-01K3R8G3N70ZMT43W6QJ7YHX4P";
const P = "P-01K3R8G3N70ZMT43W6QJ7YHX4P";
const S = `spks1-${"a".repeat(64)}`;
const SCOPE = `sha256:${"b".repeat(64)}`;

function artifact(uid, title, changes = {}) {
  return {
    uid, key: `design.search.${uid.slice(-1).toLowerCase()}`, aliases: ["oldsearchprimary"], title,
    kind: "design", status: "approved", features: ["search"], components: ["std.common.search"], layers: ["ranking"], project_uid: P,
    ...changes
  };
}

function inventory(artifacts = [
  artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "Shared Search"),
  artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4Q", "Other Design", { aliases: [], features: ["other"] })
]) {
  return deepFreeze({ snapshot: { snapshot_uid: S }, artifacts });
}

function search(input = {}) {
  return new SnapshotLexicalSearchV1({ workspace_uid: W, snapshot_uid: S, authorization_scope_digest: SCOPE, inventory: inventory(), ...input });
}

test("metadata lexical search deterministically indexes only identifiers, title, and classifications", () => {
  const first = search();
  const result = first.search({ query_text: "oldsearchprimary", limit: 100 });
  assert.deepEqual(Object.keys(result), ["snapshot_uid", "authorization_scope_digest", "logical_root", "hits", "exhausted"]);
  assert.equal(result.snapshot_uid, S);
  assert.equal(result.authorization_scope_digest, SCOPE);
  assert.match(result.logical_root, /^sha256:[a-f0-9]{64}$/);
  assert.equal(result.hits.length, 1);
  assert.equal(result.hits[0].uid, "A-01K3R8G3N70ZMT43W6QJ7YHX4P");
  assert.deepEqual(result.hits[0].matched_fields, ["identifier"]);
  assert.equal(result.exhausted, true);
  assert.equal(first.search({ query_text: "ranking", limit: 1 }).hits[0].uid, "A-01K3R8G3N70ZMT43W6QJ7YHX4P");
  assert.equal(first.search({ query_text: "nonexistent prose body", limit: 1 }).hits.length, 0);
  assert.ok(Object.isFrozen(result));
  const changed = search({ inventory: inventory([artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "Changed Title"), artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4Q", "Other Design", { aliases: [], features: ["other"] })]) });
  assert.notEqual(result.logical_root, changed.search({ query_text: "changed", limit: 1 }).logical_root);
  assert.equal(result.logical_root, search().search({ query_text: "oldsearchprimary", limit: 100 }).logical_root);
});

test("constructor rejects snapshot mismatch, duplicate UID, mutable records, extra fields, and accessors", () => {
  assert.throws(() => search({ snapshot_uid: `spks1-${"c".repeat(64)}` }), (error) => error.code === "binding_mismatch");
  const duplicate = inventory([artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "First"), artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "Second")]);
  assert.throws(() => search({ inventory: duplicate }), (error) => error.code === "binding_mismatch");
  const mutable = { snapshot: { snapshot_uid: S }, artifacts: [] };
  assert.throws(() => search({ inventory: mutable }), (error) => error.code === "invalid_request");
  const extra = deepFreeze({ snapshot: { snapshot_uid: S }, artifacts: [artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "One", { extra: "no" })] });
  assert.throws(() => search({ inventory: extra }), (error) => error.code === "invalid_request");
  const accessor = { snapshot: { snapshot_uid: S }, artifacts: [] };
  Object.defineProperty(accessor, "artifacts", { enumerable: true, configurable: false, get() { throw new Error("must not execute"); } });
  Object.freeze(accessor.snapshot); Object.freeze(accessor);
  assert.throws(() => search({ inventory: accessor }), (error) => error.code === "invalid_request");
  const sparse = { snapshot: Object.freeze({ snapshot_uid: S }), artifacts: Object.freeze(new Array(1)) };
  Object.freeze(sparse);
  assert.throws(() => search({ inventory: sparse }), (error) => error.code === "invalid_request");
  const withArrayProperty = [artifact("A-01K3R8G3N70ZMT43W6QJ7YHX4P", "One")];
  Object.defineProperty(withArrayProperty, "extra", { value: "no", enumerable: true }); Object.freeze(withArrayProperty);
  assert.throws(() => search({ inventory: Object.freeze({ snapshot: Object.freeze({ snapshot_uid: S }), artifacts: withArrayProperty }) }), (error) => error.code === "invalid_request");
});

test("search accepts only its closed non-cursor request and hard limits pages to 100", () => {
  const value = search();
  assert.throws(() => value.search({ query_text: "search", limit: 0 }), (error) => error.code === "limit_exceeded");
  assert.throws(() => value.search({ query_text: "search", limit: 101 }), (error) => error.code === "limit_exceeded");
  assert.throws(() => value.search({ query_text: "search", limit: 1, cursor: "not-supported" }), (error) => error.code === "invalid_request");
  assert.throws(() => value.search({ query_text: "search" }), (error) => error.code === "invalid_request");
});

test("source has no authority, filesystem, process, environment, network, or provider imports", async () => {
  const source = await import("node:fs/promises").then(({ readFile }) => readFile(new URL("../../src/search/snapshot_lexical.js", import.meta.url), "utf8"));
  for (const forbidden of ["node:fs", "node:child_process", "node:process", "node:net", "node:http", "node:https", "node:tls", "../provider/", "../storage/", "../workspace/", "../mcp/"]) {
    assert.equal(source.includes(forbidden), false, forbidden);
  }
});
