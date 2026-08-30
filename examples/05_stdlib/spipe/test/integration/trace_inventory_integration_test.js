import assert from "node:assert/strict";
import test from "node:test";

import { createArtifactRecord } from "../../src/model/artifact.js";
import { deepFreeze } from "../../src/model/identity.js";
import { createSectionRecord } from "../../src/model/section.js";
import { createRequirementRecord } from "../../src/model/trace.js";
import { STRICT_UNAVAILABLE_V1, createTraceInventoryV1 } from "../../src/trace/index.js";

const hash = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const uid = (prefix, digit) => `${prefix}-${digit.repeat(32)}`;

test("trace inventory composes supplied canonical records without a filesystem, authority, or provider", () => {
  const project_uid = uid("P", "1"), artifact_uid = uid("A", "2"), section_uid = uid("S", "3"), requirement_uid = uid("RQ", "4");
  const artifact = createArtifactRecord({ uid: artifact_uid, identity_status: "canonical", key: "trace.integration", project_uid, revision: "git-integration", kind: "requirements", title: "Integration", canonical_path: "doc/requirements.md", content_hash: hash, features: [], components: [], layers: [], visibility: "project", trust_scope: "untrusted_data", status: "approved", aliases: [], parser: { id: "fixture", version: 1 }, source_hash: null });
  const section = createSectionRecord({ uid: section_uid, artifact_uid, key: "trace.integration.requirement", heading: "Requirement", ordinal: 0, source_span: null, content_hash: hash, aliases: [], marker_present: true, identity_status: "canonical" });
  const requirement = createRequirementRecord({ type: "requirement", uid: requirement_uid, kind: "requirement", key: "trace.integration.requirement", display_id: "REQ-TRACE-002", project_uid, revision_id: "git-integration", artifact_uid, section_uid, title: "Integration requirement", status: "accepted", content_hash: hash, aliases: [] });
  const result = createTraceInventoryV1(deepFreeze({ snapshot_uid: uid("V", "5"), project_uid, revision_id: "git-integration", nodes: [artifact, section, requirement].sort((left, right) => left.uid.localeCompare(right.uid)), edges: [{ edge_type: "evidence_for", from_uid: artifact_uid, to_uid: requirement_uid, source_uid: artifact_uid, origin: "explicit", asserted_status: "accepted" }] }));
  assert.deepEqual(result.requirement_rows.map((row) => row.requirement_uid), [requirement_uid]);
  assert.equal(result.requirement_rows[0].declared_edges[0].strict_result, STRICT_UNAVAILABLE_V1);
});
