import {
  assertCanonicalUid, compareLexical, immutableRecord, normalizeEnum,
  normalizeRevision
} from "../model/identity.js";
import { createArtifactRecord } from "../model/artifact.js";
import { createSectionRecord } from "../model/section.js";
import {
  createRequirementRecord, createSSpecScenarioRecord, createSourceSymbolRecord,
  createTestRecord
} from "../model/trace.js";

/**
 * A bounded, supplied-data trace projection.  This module deliberately has no
 * filesystem, authority, parser, provider, persistence, search, or MCP port;
 * in particular, its output cannot satisfy a strict traceability gate.
 */
export const TRACE_NODE_TYPES_V1 = Object.freeze([
  "Artifact", "Section", "Requirement", "NFR", "SSpecScenario", "SourceSymbol", "Test"
]);
export const TRACE_EDGE_TYPES_V1 = Object.freeze([
  "evidence_for", "satisfies", "specifies", "implements", "verifies"
]);
export const TRACE_ORIGINS_V1 = Object.freeze([
  "explicit", "generated", "structural", "lexical_inference", "semantic_inference", "llm_inference"
]);
export const TRACE_ASSERTED_STATUSES_V1 = Object.freeze(["proposed", "accepted"]);
export const STRICT_UNAVAILABLE_V1 = "unavailable_without_authority";
export const MAX_TRACE_INVENTORY_NODES_V1 = 100_000;
export const MAX_TRACE_INVENTORY_EDGES_V1 = 200_000;
export const MAX_TRACE_INVENTORY_DEPTH_V1 = 32;
export const MAX_TRACE_INVENTORY_ITEMS_V1 = 400_000;
export const MAX_TRACE_INVENTORY_BYTES_V1 = 16 * 1024 * 1024;

const INVENTORY_FIELDS = ["snapshot_uid", "project_uid", "revision_id", "nodes", "edges"];
const EDGE_FIELDS = ["edge_type", "from_uid", "to_uid", "source_uid", "origin", "asserted_status"];
const ARTIFACT_FIELDS = ["type", "uid", "identity_status", "key", "project_uid", "revision", "kind", "title", "canonical_path", "content_hash", "features", "components", "layers", "visibility", "trust_scope", "status", "aliases", "parser", "source_hash"];
const SECTION_FIELDS = ["type", "uid", "artifact_uid", "key", "heading", "ordinal", "source_span", "content_hash", "aliases", "managed", "marker_present", "identity_status"];
const REQUIREMENT_FIELDS = ["type", "uid", "kind", "key", "display_id", "project_uid", "revision_id", "artifact_uid", "section_uid", "title", "status", "content_hash", "aliases"];
const SCENARIO_FIELDS = ["type", "uid", "key", "project_uid", "revision_id", "artifact_uid", "title", "ordinal", "source_location", "content_hash", "requirement_uids", "status"];
const SYMBOL_FIELDS = ["type", "uid", "project_uid", "revision_id", "canonical_path", "symbol_kind", "name", "qualified_name", "signature_hash", "source_location", "content_hash", "annotation_uids", "status"];
const TEST_FIELDS = ["type", "uid", "test_kind", "project_uid", "revision_id", "artifact_uid", "scenario_uid", "title", "source_location", "content_hash", "verifies_uids", "status"];

function ownData(value, name) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) throw new TypeError(`${name} must be a plain object`);
  if (Object.getOwnPropertySymbols(value).length) throw new TypeError(`${name} must not contain symbols`);
  return value;
}

function exactObject(value, fields, name) {
  ownData(value, name);
  const actual = Object.getOwnPropertyNames(value).sort();
  const expected = [...fields].sort();
  if (actual.join("\0") !== expected.join("\0")) throw new TypeError(`${name} fields must match the closed schema exactly`);
  for (const field of expected) {
    const descriptor = Object.getOwnPropertyDescriptor(value, field);
    if (!descriptor || !("value" in descriptor)) throw new TypeError(`${name}.${field} must be a data property`);
  }
  return value;
}

function denseArray(value, name) {
  if (!Array.isArray(value) || Object.getPrototypeOf(value) !== Array.prototype) throw new TypeError(`${name} must be a plain dense array`);
  if (Object.getOwnPropertySymbols(value).length) throw new TypeError(`${name} must not contain symbols`);
  for (let index = 0; index < value.length; index += 1) {
    if (!Object.hasOwn(value, index)) throw new TypeError(`${name} must be dense`);
    const descriptor = Object.getOwnPropertyDescriptor(value, index);
    if (!descriptor || !("value" in descriptor)) throw new TypeError(`${name}[${index}] must be a data property`);
  }
  if (Object.getOwnPropertyNames(value).some((key) => key !== "length" && (!/^(?:0|[1-9][0-9]*)$/.test(key) || Number(key) >= value.length))) throw new TypeError(`${name} must not contain extra properties`);
  return value;
}

function addItem(state) {
  state.items += 1;
  if (state.items > MAX_TRACE_INVENTORY_ITEMS_V1) throw new RangeError("trace inventory item limit exceeded");
}
function addBytes(state, text) {
  state.bytes += Buffer.byteLength(text, "utf8");
  if (state.bytes > MAX_TRACE_INVENTORY_BYTES_V1) throw new RangeError("trace inventory byte limit exceeded");
}

/**
 * Validate every *occurrence* in the supplied object graph. `active` is only
 * an ancestor stack for true cycles; `seenAliases` records completed identities
 * without suppressing an occurrence's item/byte accounting.  This ordering is
 * intentional: a shared object cannot bypass the item limit merely by being
 * seen previously, and a cycle cannot bypass it merely by being active.
 */
function assertClosedJson(value, name, state, active = new WeakSet(), seenAliases = new WeakSet(), depth = 0) {
  addItem(state);
  if (depth > MAX_TRACE_INVENTORY_DEPTH_V1) throw new RangeError("trace inventory nesting depth limit exceeded");
  if (value === null || typeof value === "boolean") return;
  if (typeof value === "string") { addBytes(state, value); return; }
  if (typeof value === "number") {
    if (!Number.isFinite(value)) throw new TypeError(`${name} must contain finite JSON numbers only`);
    return;
  }
  if (!value || typeof value !== "object") throw new TypeError(`${name} must contain JSON data only`);
  if (active.has(value)) throw new TypeError(`${name} must not contain recursive cycles`);
  if (seenAliases.has(value)) return;
  active.add(value);
  if (Array.isArray(value)) {
    denseArray(value, name);
    for (let index = 0; index < value.length; index += 1) {
      const descriptor = Object.getOwnPropertyDescriptor(value, index);
      assertClosedJson(descriptor.value, `${name}[${index}]`, state, active, seenAliases, depth + 1);
    }
  } else {
    ownData(value, name);
    for (const key of Object.getOwnPropertyNames(value)) {
      const descriptor = Object.getOwnPropertyDescriptor(value, key);
      if (!descriptor || !("value" in descriptor)) throw new TypeError(`${name}.${key} must be a data property`);
      addBytes(state, key);
      assertClosedJson(descriptor.value, `${name}.${key}`, state, active, seenAliases, depth + 1);
    }
  }
  active.delete(value);
  seenAliases.add(value);
}

function recursivelyFrozen(value, seen = new WeakSet()) {
  if (!value || typeof value !== "object") return true;
  if (!Object.isFrozen(value)) return false;
  if (seen.has(value)) return true;
  seen.add(value);
  for (const key of Object.getOwnPropertyNames(value)) {
    if (Array.isArray(value) && key === "length") continue;
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (!descriptor || !("value" in descriptor) || !recursivelyFrozen(descriptor.value, seen)) return false;
  }
  return true;
}

function sourceLocationShape(value, name) {
  exactObject(value, ["source_artifact_uid", "source_hash", "span"], name);
  exactObject(value.span, ["start_byte", "end_byte"], `${name}.span`);
}
function rawNodeKind(raw) {
  switch (raw.type) {
    case "artifact": return "Artifact";
    case "section": return "Section";
    case "requirement": return "Requirement";
    case "non_functional_requirement": return "NFR";
    case "sspec_scenario": return "SSpecScenario";
    case "source_symbol": return "SourceSymbol";
    case "test": return "Test";
    default: throw new TypeError("trace node type is not in the closed TraceInventoryV1 vocabulary");
  }
}
function normalizeNode(raw) {
  const kind = rawNodeKind(raw);
  if (kind === "Artifact") {
    exactObject(raw, ARTIFACT_FIELDS, "artifact"); exactObject(raw.parser, ["id", "version"], "artifact.parser");
    const record = createArtifactRecord(raw);
    if (record.identity_status !== "canonical") throw new TypeError("trace inventory artifacts must have canonical identity");
    return { kind, record };
  }
  if (kind === "Section") {
    exactObject(raw, SECTION_FIELDS, "section");
    if (raw.source_span !== null) exactObject(raw.source_span, ["start_byte", "end_byte"], "section.source_span");
    if (raw.managed !== true || raw.marker_present !== true || raw.identity_status !== "canonical") throw new TypeError("section canonical values are required");
    return { kind, record: createSectionRecord(raw) };
  }
  if (kind === "Requirement" || kind === "NFR") return { kind, record: createRequirementRecord(exactObject(raw, REQUIREMENT_FIELDS, "requirement")) };
  if (kind === "SSpecScenario") { exactObject(raw, SCENARIO_FIELDS, "sspec scenario"); sourceLocationShape(raw.source_location, "scenario.source_location"); return { kind, record: createSSpecScenarioRecord(raw) }; }
  if (kind === "SourceSymbol") { exactObject(raw, SYMBOL_FIELDS, "source symbol"); sourceLocationShape(raw.source_location, "symbol.source_location"); return { kind, record: createSourceSymbolRecord(raw) }; }
  exactObject(raw, TEST_FIELDS, "test"); sourceLocationShape(raw.source_location, "test.source_location"); return { kind, record: createTestRecord(raw) };
}

function ownerArtifactUid(node) {
  if (node.kind === "Artifact") return node.record.uid;
  if (node.kind === "SourceSymbol") return node.record.source_location.source_artifact_uid;
  return node.record.artifact_uid;
}
function requireNode(nodes, uid, kinds, name) {
  const node = nodes.get(uid);
  if (!node || !kinds.includes(node.kind)) throw new TypeError(`${name} must name a present ${kinds.join(" or ")} node`);
  return node;
}
function assertScope(node, header, nodes) {
  const artifact = requireNode(nodes, ownerArtifactUid(node), ["Artifact"], `trace node ${node.record.uid} source artifact`);
  if (artifact.record.project_uid !== header.project_uid || artifact.record.revision !== header.revision_id) throw new TypeError("trace source artifact must belong to the inventory project and revision");
  if (!["Artifact", "Section"].includes(node.kind) && (node.record.project_uid !== header.project_uid || node.record.revision_id !== header.revision_id)) throw new TypeError("trace node must belong to the inventory project and revision");
  if (["Requirement", "NFR"].includes(node.kind)) {
    const section = requireNode(nodes, node.record.section_uid, ["Section"], "requirement section_uid");
    if (section.record.artifact_uid !== node.record.artifact_uid) throw new TypeError("requirement section must belong to its source artifact");
  }
  if (node.kind === "SSpecScenario") for (const uid of node.record.requirement_uids) requireNode(nodes, uid, ["Requirement", "NFR"], "scenario requirement entry");
  if (node.kind === "SourceSymbol") for (const uid of node.record.annotation_uids) requireNode(nodes, uid, ["Requirement", "NFR", "SSpecScenario"], "symbol annotation entry");
  if (node.kind === "Test") {
    if (node.record.scenario_uid !== null) requireNode(nodes, node.record.scenario_uid, ["SSpecScenario"], "test scenario_uid");
    for (const uid of node.record.verifies_uids) requireNode(nodes, uid, ["Requirement", "NFR", "SSpecScenario", "SourceSymbol"], "test verifies entry");
  }
}
function endpointAllowed(type, from, to) {
  const requirement = to === "Requirement" || to === "NFR";
  if (type === "evidence_for") return ["Artifact", "Section"].includes(from) && requirement;
  if (type === "satisfies") return ["Artifact", "Section", "SourceSymbol"].includes(from) && requirement;
  if (type === "specifies") return from === "SSpecScenario" && requirement;
  if (type === "implements") return from === "SourceSymbol" && (requirement || to === "SSpecScenario");
  return type === "verifies" && from === "Test" && (requirement || to === "SSpecScenario" || to === "SourceSymbol");
}
function edgeKey(edge) { return `${edge.from_uid}\0${edge.edge_type}\0${edge.to_uid}\0${edge.source_uid}`; }
function normalizeEdges(rawEdges, nodes) {
  const edges = []; let previous = null;
  for (const raw of rawEdges) {
    exactObject(raw, EDGE_FIELDS, "trace edge");
    const edge = { edge_type: normalizeEnum(raw.edge_type, TRACE_EDGE_TYPES_V1, "edge_type"), from_uid: assertCanonicalUid(raw.from_uid, "from_uid"), to_uid: assertCanonicalUid(raw.to_uid, "to_uid"), source_uid: assertCanonicalUid(raw.source_uid, "source_uid"), origin: normalizeEnum(raw.origin, TRACE_ORIGINS_V1, "origin"), asserted_status: normalizeEnum(raw.asserted_status, TRACE_ASSERTED_STATUSES_V1, "asserted_status") };
    const key = edgeKey(edge);
    if (previous !== null && compareLexical(previous, key) >= 0) throw new TypeError("trace edges must be strictly sorted; duplicate semantic occurrences are forbidden");
    previous = key;
    const from = requireNode(nodes, edge.from_uid, TRACE_NODE_TYPES_V1, "trace edge from_uid");
    const to = requireNode(nodes, edge.to_uid, TRACE_NODE_TYPES_V1, "trace edge to_uid");
    requireNode(nodes, edge.source_uid, TRACE_NODE_TYPES_V1, "trace edge source_uid");
    if (edge.from_uid === edge.to_uid || !endpointAllowed(edge.edge_type, from.kind, to.kind)) throw new TypeError("trace edge endpoint types are not allowed by the closed vocabulary");
    if (edge.asserted_status === "accepted" && !["explicit", "generated"].includes(edge.origin)) throw new TypeError("inferred trace links cannot be asserted accepted");
    edges.push(immutableRecord({ ...edge, declaration_status: "declared", strict_result: STRICT_UNAVAILABLE_V1 }));
  }
  return edges;
}

/** Validate bounded supplied facts and return an immutable, deterministic view. */
export function createTraceInventoryV1(input) {
  exactObject(input, INVENTORY_FIELDS, "TraceInventoryV1 input");
  denseArray(input.nodes, "nodes"); denseArray(input.edges, "edges");
  if (input.nodes.length > MAX_TRACE_INVENTORY_NODES_V1) throw new RangeError("trace node limit exceeded");
  if (input.edges.length > MAX_TRACE_INVENTORY_EDGES_V1) throw new RangeError("trace edge limit exceeded");
  assertClosedJson(input, "TraceInventoryV1 input", { items: 0, bytes: 0 });
  if (!recursivelyFrozen(input)) throw new TypeError("TraceInventoryV1 input must be recursively frozen");
  const header = { snapshot_uid: assertCanonicalUid(input.snapshot_uid, "snapshot_uid", ["V"]), project_uid: assertCanonicalUid(input.project_uid, "project_uid", ["P"]), revision_id: normalizeRevision(input.revision_id, "revision_id") };
  const nodes = new Map(); let previous = null;
  for (const raw of input.nodes) {
    const node = normalizeNode(raw);
    if (previous !== null && compareLexical(previous, node.record.uid) >= 0) throw new TypeError("trace nodes must be strictly sorted and unique by uid");
    previous = node.record.uid; nodes.set(node.record.uid, node);
  }
  for (const node of nodes.values()) assertScope(node, header, nodes);
  const edges = normalizeEdges(input.edges, nodes);
  // Each admitted edge has at most two endpoints.  Building this adjacency
  // once keeps declared-cap processing O(nodes + edges), rather than scanning
  // all edges once for every requirement row.
  const requirement_nodes = [...nodes.values()].filter((node) => ["Requirement", "NFR"].includes(node.kind));
  const adjacency = new Map(requirement_nodes.map((node) => [node.record.uid, []]));
  for (const edge of edges) {
    if (adjacency.has(edge.from_uid)) adjacency.get(edge.from_uid).push(edge);
    if (adjacency.has(edge.to_uid)) adjacency.get(edge.to_uid).push(edge);
  }
  const requirement_rows = requirement_nodes.map((node) => immutableRecord({ requirement_uid: node.record.uid, requirement_type: node.kind, declared_edges: adjacency.get(node.record.uid), strict_result: STRICT_UNAVAILABLE_V1 }));
  return immutableRecord({ type: "TraceInventoryV1", ...header, nodes: [...nodes.values()].map((node) => immutableRecord({ node_type: node.kind, ...node.record })), edges, requirement_rows, strict_result: STRICT_UNAVAILABLE_V1 });
}
export const TraceInventoryV1 = createTraceInventoryV1;
