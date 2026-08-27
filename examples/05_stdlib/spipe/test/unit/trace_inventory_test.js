import assert from "node:assert/strict";
import test from "node:test";

import { createArtifactRecord } from "../../src/model/artifact.js";
import { deepFreeze } from "../../src/model/identity.js";
import { createSectionRecord } from "../../src/model/section.js";
import {
  createRequirementRecord, createSSpecScenarioRecord, createSourceSymbolRecord,
  createTestRecord
} from "../../src/model/trace.js";
import {
  MAX_TRACE_INVENTORY_DEPTH_V1, MAX_TRACE_INVENTORY_EDGES_V1,
  MAX_TRACE_INVENTORY_BYTES_V1, MAX_TRACE_INVENTORY_ITEMS_V1, MAX_TRACE_INVENTORY_NODES_V1,
  STRICT_UNAVAILABLE_V1, createTraceInventoryV1
} from "../../src/trace/index.js";

const hash = `sha256:${"a".repeat(64)}`;
const uid = (prefix, digit) => `${prefix}-${digit.repeat(32)}`;
const PROJECT = uid("P", "1"), SNAPSHOT = uid("V", "2"), REVISION = "git-trace-fixture";
const DOC = uid("A", "3"), SPEC = uid("A", "4"), SOURCE = uid("A", "5"), TEST_DOC = uid("A", "6");
const SECTION = uid("S", "7"), REQUIREMENT = uid("RQ", "8"), SCENARIO = uid("SS", "9"), SYMBOL = uid("SY", "A"), TEST = uid("T", "B");

function artifact(value, path, kind = "source") {
  return createArtifactRecord({ uid: value, identity_status: "canonical", key: `trace.${value.slice(0, 2).toLowerCase()}.${value.at(-1).toLowerCase()}`,
    project_uid: PROJECT, revision: REVISION, kind, title: path, canonical_path: path, content_hash: hash,
    features: [], components: [], layers: [], visibility: "project", trust_scope: "untrusted_data", status: "approved", aliases: [], parser: { id: "fixture", version: 1 }, source_hash: null });
}
function location(source_artifact_uid) { return { source_artifact_uid, source_hash: hash, span: { start_byte: 0, end_byte: 0 } }; }
function edgeKey(edge) { return `${edge.from_uid}\0${edge.edge_type}\0${edge.to_uid}\0${edge.source_uid}`; }
function fixture() {
  const section = createSectionRecord({ uid: SECTION, artifact_uid: DOC, key: "trace.requirement", heading: "Requirement", ordinal: 0, source_span: null, content_hash: hash, aliases: [], marker_present: true, identity_status: "canonical" });
  const requirement = createRequirementRecord({ type: "requirement", uid: REQUIREMENT, kind: "requirement", key: "trace.requirement", display_id: "REQ-TRACE-001", project_uid: PROJECT, revision_id: REVISION, artifact_uid: DOC, section_uid: SECTION, title: "Trace inventory", status: "accepted", content_hash: hash, aliases: [] });
  const scenario = createSSpecScenarioRecord({ type: "sspec_scenario", uid: SCENARIO, key: "trace.scenario", project_uid: PROJECT, revision_id: REVISION, artifact_uid: SPEC, title: "declares trace", ordinal: 0, source_location: location(SPEC), content_hash: hash, requirement_uids: [REQUIREMENT], status: "accepted" });
  const symbol = createSourceSymbolRecord({ type: "source_symbol", uid: SYMBOL, project_uid: PROJECT, revision_id: REVISION, canonical_path: "src/feature.spl", symbol_kind: "function", name: "feature", qualified_name: "feature", signature_hash: hash, source_location: location(SOURCE), content_hash: hash, annotation_uids: [REQUIREMENT], status: "accepted" });
  const testRecord = createTestRecord({ type: "test", uid: TEST, test_kind: "unit", project_uid: PROJECT, revision_id: REVISION, artifact_uid: TEST_DOC, scenario_uid: SCENARIO, title: "feature test", source_location: location(TEST_DOC), content_hash: hash, verifies_uids: [REQUIREMENT], status: "accepted" });
  const nodes = [artifact(DOC, "doc/research.md", "research"), artifact(SPEC, "test/spec.spl", "spec"), artifact(SOURCE, "src/feature.spl"), artifact(TEST_DOC, "test/feature.spl", "test"), section, requirement, scenario, symbol, testRecord].sort((a, b) => a.uid.localeCompare(b.uid));
  const edges = [
    { edge_type: "evidence_for", from_uid: DOC, to_uid: REQUIREMENT, source_uid: DOC, origin: "explicit", asserted_status: "accepted" },
    { edge_type: "specifies", from_uid: SCENARIO, to_uid: REQUIREMENT, source_uid: SCENARIO, origin: "explicit", asserted_status: "accepted" },
    { edge_type: "implements", from_uid: SYMBOL, to_uid: REQUIREMENT, source_uid: SYMBOL, origin: "generated", asserted_status: "accepted" },
    { edge_type: "verifies", from_uid: TEST, to_uid: REQUIREMENT, source_uid: TEST, origin: "explicit", asserted_status: "accepted" }
  ].sort((a, b) => edgeKey(a).localeCompare(edgeKey(b)));
  return { snapshot_uid: SNAPSHOT, project_uid: PROJECT, revision_id: REVISION, nodes, edges };
}

test("TraceInventoryV1 is immutable, deterministic, requirement-centric, and never strict authority evidence", () => {
  assert.throws(() => createTraceInventoryV1(fixture()), /recursively frozen/);
  const result = createTraceInventoryV1(deepFreeze(fixture()));
  assert.equal(result.strict_result, STRICT_UNAVAILABLE_V1);
  assert.equal(result.requirement_rows.length, 1);
  assert.deepEqual(result.requirement_rows[0].declared_edges.map((edge) => edge.edge_type), ["evidence_for", "specifies", "implements", "verifies"]);
  assert.ok(Object.isFrozen(result));
  assert.ok(Object.isFrozen(result.requirement_rows[0].declared_edges));
  assert.throws(() => result.edges.push({}), TypeError);
});

test("TraceInventoryV1 closes input shape, scope, edge semantics, and inference claims", () => {
  const getter = fixture();
  getter.nodes[0] = { ...getter.nodes[0] };
  Object.defineProperty(getter.nodes[0], "type", { enumerable: true, get: () => "artifact" });
  assert.throws(() => createTraceInventoryV1(getter), /data property/);
  const proto = fixture(); proto.edges[0] = Object.assign(Object.create({ inherited: true }), proto.edges[0]);
  assert.throws(() => createTraceInventoryV1(proto), /plain object/);
  const endpoint = fixture(); endpoint.edges[0] = { ...endpoint.edges[0], edge_type: "verifies" };
  assert.throws(() => createTraceInventoryV1(deepFreeze(endpoint)), /endpoint/);
  const foreign = fixture(); foreign.nodes = foreign.nodes.map((node) => node.uid === SYMBOL ? { ...node, revision_id: "git-other" } : node);
  assert.throws(() => createTraceInventoryV1(deepFreeze(foreign)), /project and revision/);
  const inferred = fixture(); inferred.edges[0] = { ...inferred.edges[0], origin: "semantic_inference" };
  assert.throws(() => createTraceInventoryV1(deepFreeze(inferred)), /inferred trace links/);
});

test("TraceInventoryV1 has strict semantic ordering and supplied-input bounds", () => {
  const input = fixture();
  assert.throws(() => createTraceInventoryV1(deepFreeze({ ...input, nodes: [...input.nodes].reverse() })), /sorted/);
  assert.throws(() => createTraceInventoryV1({ ...input, nodes: Array(MAX_TRACE_INVENTORY_NODES_V1 + 1).fill(input.nodes[0]) }), /node limit/);
  assert.throws(() => createTraceInventoryV1({ ...input, edges: Array(MAX_TRACE_INVENTORY_EDGES_V1 + 1).fill(input.edges[0]) }), /edge limit/);
  const deep = fixture(); deep.nodes[0] = { ...deep.nodes[0], parser: { id: "fixture", version: 1 } };
  let cursor = deep.nodes[0].parser;
  for (let index = 0; index <= MAX_TRACE_INVENTORY_DEPTH_V1; index += 1) { cursor.child = {}; cursor = cursor.child; }
  assert.throws(() => createTraceInventoryV1(deep), /depth limit/);
  const tooManyBytes = fixture(); tooManyBytes.nodes[0] = { ...tooManyBytes.nodes[0], title: "x".repeat(MAX_TRACE_INVENTORY_BYTES_V1 + 1) };
  assert.throws(() => createTraceInventoryV1(tooManyBytes), /byte limit/);

  const repeated = fixture(); repeated.edges = [repeated.edges[0], repeated.edges[0]];
  assert.throws(() => createTraceInventoryV1(deepFreeze(repeated)), /duplicate semantic occurrences/);
  const sameKeyDifferentStatus = fixture();
  sameKeyDifferentStatus.edges = [sameKeyDifferentStatus.edges[0], { ...sameKeyDifferentStatus.edges[0], asserted_status: "proposed" }];
  assert.throws(() => createTraceInventoryV1(deepFreeze(sameKeyDifferentStatus)), /duplicate semantic occurrences/);
});

test("TraceInventoryV1 counts every aliased occurrence before alias/cycle checks", () => {
  const input = fixture();
  const shared = {};
  input.nodes[0] = { ...input.nodes[0], parser: { id: "fixture", version: 1, shared } };
  for (let index = 0; index < MAX_TRACE_INVENTORY_ITEMS_V1; index += 1) input.nodes[0].parser[`alias${index}`] = shared;
  assert.throws(() => createTraceInventoryV1(input), /item limit/);

  const cyclic = fixture();
  cyclic.nodes[0] = { ...cyclic.nodes[0], parser: { id: "fixture", version: 1 } };
  cyclic.nodes[0].parser.self = cyclic.nodes[0].parser;
  assert.throws(() => createTraceInventoryV1(cyclic), /recursive cycles/);

  // The traversal sees six values before the padding: envelope, three header
  // scalars, nodes array, and raw node. `self` must therefore be item M + 1.
  // If cycle detection ran before accounting, this would report a cycle instead.
  const raw = {};
  for (let index = 0; index < MAX_TRACE_INVENTORY_ITEMS_V1 - 6; index += 1) raw[`near_cap_${index}`] = null;
  raw.self = raw;
  const cappedCycle = { snapshot_uid: SNAPSHOT, project_uid: PROJECT, revision_id: REVISION, nodes: [raw], edges: [] };
  assert.throws(() => createTraceInventoryV1(cappedCycle), /item limit/);
});
