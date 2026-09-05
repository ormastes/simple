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
  MAX_TRACE_INVENTORY_EDGES_V1, MAX_TRACE_INVENTORY_NODES_V1,
  MAX_TRACE_INVENTORY_DEPTH_V1, MAX_TRACE_INVENTORY_BYTES_V1,
  MAX_TRACE_INVENTORY_ITEMS_V1,
  STRICT_UNAVAILABLE_V1, createTraceInventoryV1
} from "../../src/trace/index.js";

const hash = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const uid = (prefix, digit) => `${prefix}-${digit.repeat(32)}`;
const PROJECT = uid("P", "1"), SNAPSHOT = uid("V", "2"), REVISION = "git-trace-fixture";
const DOC = uid("A", "3"), SPEC = uid("A", "4"), SOURCE = uid("A", "5"), TEST_DOC = uid("A", "6");
const SECTION = uid("S", "7"), REQUIREMENT = uid("RQ", "8"), SCENARIO = uid("SS", "9"), SYMBOL = uid("SY", "A"), TEST = uid("T", "B");

function artifact(uidValue, path, kind = "source") {
  return createArtifactRecord({ uid: uidValue, identity_status: "canonical", key: `trace.${uidValue.slice(0, 2).toLowerCase()}.${uidValue.at(-1).toLowerCase()}`,
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
  ].sort((left, right) => edgeKey(left).localeCompare(edgeKey(right)));
  return { snapshot_uid: SNAPSHOT, project_uid: PROJECT, revision_id: REVISION, nodes, edges };
}

test("TraceInventoryV1 is immutable, deterministic, requirement-centric, and strict-unavailable", () => {
  assert.throws(() => createTraceInventoryV1(fixture()), /recursively frozen/);
  const result = createTraceInventoryV1(deepFreeze(fixture()));
  assert.equal(result.strict_result, STRICT_UNAVAILABLE_V1);
  assert.equal(result.requirement_rows.length, 1);
  assert.equal(result.requirement_rows[0].requirement_uid, REQUIREMENT);
  assert.equal(result.requirement_rows[0].declared_edges.length, 4);
  assert.ok(Object.isFrozen(result));
  assert.ok(Object.isFrozen(result.nodes));
  assert.ok(Object.isFrozen(result.requirement_rows[0].declared_edges));
  for (const edge of result.edges) assert.equal(edge.strict_result, STRICT_UNAVAILABLE_V1);
  assert.throws(() => result.edges.push({}), TypeError);
});

test("TraceInventoryV1 rejects accessor, prototype, endpoint, scope, and inferred-accepted input", () => {
  const getter = fixture();
  getter.nodes[0] = { ...getter.nodes[0] };
  Object.defineProperty(getter.nodes[0], "type", { enumerable: true, get: () => "artifact" });
  assert.throws(() => createTraceInventoryV1(getter), /data property/);
  const hiddenGetter = fixture();
  hiddenGetter.nodes[0] = { ...hiddenGetter.nodes[0], parser: { ...hiddenGetter.nodes[0].parser } };
  Object.defineProperty(hiddenGetter.nodes[0].parser, "hidden", { get: () => "no" });
  assert.throws(() => createTraceInventoryV1(hiddenGetter), /fields must match|data property/);
  const arrayGetter = fixture();
  const first = arrayGetter.nodes[0];
  Object.defineProperty(arrayGetter.nodes, "0", { configurable: true, enumerable: true, get: () => first });
  Object.freeze(arrayGetter.nodes); Object.freeze(arrayGetter);
  assert.throws(() => createTraceInventoryV1(arrayGetter), /data property/);
  const parserExtra = fixture(); parserExtra.nodes[0] = { ...parserExtra.nodes[0], parser: { ...parserExtra.nodes[0].parser, unexpected: true } };
  assert.throws(() => createTraceInventoryV1(deepFreeze(parserExtra)), /fields must match/);
  const spanExtra = fixture(); const sectionIndex = spanExtra.nodes.findIndex((node) => node.uid === SECTION);
  spanExtra.nodes[sectionIndex] = { ...spanExtra.nodes[sectionIndex], source_span: { start_byte: 0, end_byte: 0, unexpected: true } };
  assert.throws(() => createTraceInventoryV1(deepFreeze(spanExtra)), /fields must match/);
  const rewrittenSection = fixture(); const rewrittenIndex = rewrittenSection.nodes.findIndex((node) => node.uid === SECTION);
  rewrittenSection.nodes[rewrittenIndex] = { ...rewrittenSection.nodes[rewrittenIndex], managed: false };
  assert.throws(() => createTraceInventoryV1(deepFreeze(rewrittenSection)), /canonical values/);
  const prototype = fixture(); prototype.edges[0] = Object.assign(Object.create({ inherited: true }), prototype.edges[0]);
  assert.throws(() => createTraceInventoryV1(prototype), /plain object/);
  const badEndpoint = fixture(); badEndpoint.edges[0] = { ...badEndpoint.edges[0], edge_type: "verifies" };
  assert.throws(() => createTraceInventoryV1(deepFreeze(badEndpoint)), /endpoint/);
  const foreign = fixture(); foreign.nodes = foreign.nodes.map((node) => node.uid === SYMBOL ? { ...node, revision_id: "git-other" } : node);
  assert.throws(() => createTraceInventoryV1(deepFreeze(foreign)), /project and revision/);
  const inferred = fixture(); inferred.edges[0] = { ...inferred.edges[0], origin: "semantic_inference" };
  assert.throws(() => createTraceInventoryV1(deepFreeze(inferred)), /inferred trace links/);
});

test("TraceInventoryV1 reports repeated edge data as a duplicate semantic occurrence, not a recursive cycle", () => {
  const repeated = fixture();
  const edge = repeated.edges[0];
  repeated.edges = [edge, edge];
  assert.throws(() => createTraceInventoryV1(deepFreeze(repeated)), /duplicate semantic occurrences/);
  const recursive = fixture();
  recursive.nodes[0] = { ...recursive.nodes[0], parser: { id: "fixture", version: 1 } };
  recursive.nodes[0].parser.self = recursive.nodes[0].parser;
  assert.throws(() => createTraceInventoryV1(recursive), /recursive cycles/);
});

test("TraceInventoryV1 enforces ordering and bounded supplied input before record decoding", () => {
  const input = fixture();
  assert.throws(() => createTraceInventoryV1(deepFreeze({ ...input, nodes: [...input.nodes].reverse() })), /sorted/);
  assert.throws(() => createTraceInventoryV1({ ...input, nodes: Array(MAX_TRACE_INVENTORY_NODES_V1 + 1).fill(input.nodes[0]) }), /node limit/);
  assert.throws(() => createTraceInventoryV1({ ...input, edges: Array(MAX_TRACE_INVENTORY_EDGES_V1 + 1).fill(input.edges[0]) }), /edge limit/);
  const deep = fixture(); deep.nodes[0] = { ...deep.nodes[0], parser: { id: "fixture", version: 1 } };
  let cursor = deep.nodes[0].parser;
  for (let index = 0; index <= MAX_TRACE_INVENTORY_DEPTH_V1; index += 1) { cursor.child = {}; cursor = cursor.child; }
  assert.throws(() => createTraceInventoryV1(deep), /depth limit/);
  const tooManyItems = fixture(); tooManyItems.nodes[0] = { ...tooManyItems.nodes[0], features: Array(MAX_TRACE_INVENTORY_ITEMS_V1 + 1).fill("x") };
  assert.throws(() => createTraceInventoryV1(deepFreeze(tooManyItems)), /item limit/);
  const tooManyBytes = fixture(); tooManyBytes.nodes[0] = { ...tooManyBytes.nodes[0], title: "x".repeat(MAX_TRACE_INVENTORY_BYTES_V1 + 1) };
  assert.throws(() => createTraceInventoryV1(deepFreeze(tooManyBytes)), /byte limit/);
});
