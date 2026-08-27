import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import test from "node:test";

import {
  SnapshotAuthorityNonAdmissionError, SnapshotAuthorityPortV1, isSnapshotAuthorityPortV1
} from "../../src/core/snapshot_authority_port.js";

const BINDING = Object.freeze({
  workspaceUid: "W-00000000000000000000000000000001",
  projectUidOrNull: null,
  worktreeUid: "W-00000000000000000000000000000002",
  baseSnapshotUid: "spks1-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  authoritySnapshotUid: "spks1-bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  revisionId: "git:abcdef",
  registryRevisionId: "rr-1"
});

function closedFailure(thunk, code = "SPKSA001") {
  assert.throws(thunk, (error) => error instanceof SnapshotAuthorityNonAdmissionError && error.code === code);
}

test("sealed non-admitted port has an exact immutable public surface", () => {
  assert.equal(isSnapshotAuthorityPortV1(SnapshotAuthorityPortV1), true);
  assert.equal(isSnapshotAuthorityPortV1({ ...SnapshotAuthorityPortV1 }), false);
  assert.equal(Object.isFrozen(SnapshotAuthorityPortV1), true);
  assert.deepEqual(Object.keys(SnapshotAuthorityPortV1).sort(), [
    "createExpectedReadBindingV1", "isCanonicalTargetCandidateV1", "isDirectoryTargetCandidateV1",
    "isExpectedReadBindingV1", "isSnapshotAuthorityViewV1", "listDirectoryTarget", "openBoundSnapshot",
    "resolveCanonicalTarget"
  ]);
});

test("open validates every closed seven-coordinate binding before non-admission", () => {
  for (const field of Object.keys(BINDING)) {
    const mutated = { ...BINDING, [field]: field === "projectUidOrNull" ? 42 : "" };
    closedFailure(() => SnapshotAuthorityPortV1.openBoundSnapshot(mutated));
  }
  closedFailure(() => SnapshotAuthorityPortV1.openBoundSnapshot({ ...BINDING, forgedManifest: {} }));
  closedFailure(() => SnapshotAuthorityPortV1.openBoundSnapshot(Object.create(BINDING)));
  const accessor = { ...BINDING };
  Object.defineProperty(accessor, "revisionId", { enumerable: true, get: () => "git:forged" });
  closedFailure(() => SnapshotAuthorityPortV1.openBoundSnapshot(accessor));
});

test("well-formed binding fails closed because no durable published inventory exists", () => {
  closedFailure(() => SnapshotAuthorityPortV1.openBoundSnapshot({ ...BINDING }), "SPKSA003");
});

test("opaque view, candidates, and expected binding cannot be forged or turned into a positive open", () => {
  const forged = Object.freeze({ binding: BINDING, authorityManifestDigest: "sha256:forged" });
  assert.equal(SnapshotAuthorityPortV1.isSnapshotAuthorityViewV1(forged), false);
  assert.equal(SnapshotAuthorityPortV1.isCanonicalTargetCandidateV1(forged), false);
  assert.equal(SnapshotAuthorityPortV1.isDirectoryTargetCandidateV1(forged), false);
  assert.equal(SnapshotAuthorityPortV1.isExpectedReadBindingV1(forged), false);
  closedFailure(() => SnapshotAuthorityPortV1.resolveCanonicalTarget(forged, forged), "SPKSA002");
  closedFailure(() => SnapshotAuthorityPortV1.listDirectoryTarget(forged, forged), "SPKSA002");
  closedFailure(() => SnapshotAuthorityPortV1.createExpectedReadBindingV1(forged, forged, {}), "SPKSA002");
});

test("kernel source imports no forbidden authority widening surface", () => {
  const source = readFileSync(new URL("../../src/core/snapshot_authority_port.js", import.meta.url), "utf8");
  assert.doesNotMatch(source, /^import\s/m);
  assert.doesNotMatch(source, /(?:\.\.?\/)+(?:storage|view|mcp|uri|cursor|workspace)\//);
  assert.doesNotMatch(source, /\b(?:create|install|configure)[A-Z][A-Za-z]*SnapshotAuthority/);
  assert.match(source, /authorityInstanceUid/);
  assert.match(source, /authorityManifestDigest/);
});
