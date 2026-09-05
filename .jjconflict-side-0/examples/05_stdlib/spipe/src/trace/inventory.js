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
 * TraceInventoryV1 is a supplied-data projection only.  In particular, it has
 * no authority, persistence, filesystem, parser, provider, search, MCP, or
 * authentication port.  Its declared rows are deliberately insufficient to
 * certify a strict trace gate.
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

function plainDataObject(value, fields, name) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) {
    throw new TypeError(`${name} must be a plain object`);
  }
  if (Object.getOwnPropertySymbols(value).length) throw new TypeError(`${name} must not contain symbols`);
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
    if (!Object.prototype.hasOwnProperty.call(value, index)) throw new TypeError(`${name} must be dense`);
    const descriptor = Object.getOwnPropertyDescriptor(value, index);
    if (!descriptor || !("value" in descriptor)) throw new TypeError(`${name}[${index}] must be a data property`);
  }
  if (Object.getOwnPropertyNames(value).some((key) => key !== "length" && (!/^(?:0|[1-9][0-9]*)$/.test(key) || Number(key) >= value.length))) {
    throw new TypeError(`${name} must not contain extra properties`);
  }
  return value;
}

/**
 * Accept JSON-shaped values only.  `active` detects a real recursive cycle;
 * `visited` permits an aliased object to occur twice, so a repeated supplied
 * edge is diagnosed later as a duplicate semantic occurrence rather than as a
 * fake object-graph cycle.
 */
function assertClosedJson(value, name, state, active = new WeakSet(), visited = new WeakSet(), depth = 0) {
  const countItem = () => {
    state.items += 1;
    if (state.items > MAX_TRACE_INVENTORY_ITEMS_V1) throw new RangeError("trace inventory item limit exceeded");
  };
  if (depth > MAX_TRACE_INVENTORY_DEPTH_V1) throw new RangeError("trace inventory nesting depth limit exceeded");
  if (value === null || typeof value === "boolean") { countItem(); return; }
  if (typeof value === "string") {
    countItem();
    state.bytes += Buffer.byteLength(value, "utf8");
    if (state.bytes > MAX_TRACE_INVENTORY_BYTES_V1) throw new RangeError("trace inventory byte limit exceeded");
    return;
  }
  if (typeof value === "number") {
    if (!Number.isFinite(value)) throw new TypeError(`${name} must contain finite JSON numbers only`);
    countItem();
    return;
  }
  if (!value || typeof value !== "object") throw new TypeError(`${name} must contain JSON data only`);
  if (active.has(value)) throw new TypeError(`${name} must not contain recursive cycles`);
  if (visited.has(value)) return;
  active.add(value);
  countItem();
  if (Array.isArray(value)) {
    denseArray(value, name);
    for (let index = 0; index < value.length; index += 1) {
      const descriptor = Object.getOwnPropertyDescriptor(value, index);
      assertClosedJson(descriptor.value, `${name}[${index}]`, state, active, visited, depth + 1);
    }
  } else {
    if (Object.getPrototypeOf(value) !== Object.prototype || Object.getOwnPropertySymbols(value).length) {
      throw new TypeError(`${name} must be a plain object without symbols`);
    }
    for (const key of Object.getOwnPropertyNames(value)) {
      const descriptor = Object.getOwnPropertyDescriptor(value, key);
      if (!descriptor || !("value" in descriptor)) throw new TypeError(`${name}.${key} must be a data property`);
      state.bytes += Buffer.byteLength(key, "utf8");
      if (state.bytes > MAX_TRACE_INVENTORY_BYTES_V1) throw new RangeError("trace inventory byte limit exceeded");
      assertClosedJson(descriptor.value, `${name}.${key}`, state, active, visited, depth + 1);
    }
  }
  active.delete(value);
  visited.add(value);
}

function isRecursivelyFrozen(value, seen = new WeakSet()) {
  if (!value || typeof value !== "object") return true;
  if (!Object.isFrozen(value) || seen.has(value)) return Object.isFrozen(value);
  seen.add(value);
  for (const key of Object.getOwnPropertyNames(value)) {
    if (Array.isArray(value) && key === "length") continue;
    const descriptor = Object.getOwnPropertyDescriptor(value, key);
    if (!descriptor || !("value" in descriptor) || !isRecursivelyFrozen(descriptor.value, seen)) return false;
  }
  return true;
}

function exactNested(value, fields, name) { return plainDataObject(value, fields, name); }
function sourceLocationShape(value, name) {
  exactNested(value, ["source_artifact_uid", "source_hash", "span"], name);
  exactNested(value.span, ["start_byte", "end_byte"], `${name}.span`);
}
function assertNodeNestedShape(raw, kind) {
  if (kind === "Artifact") exactNested(raw.parser, ["id", "version"], "artifact.parser");
  if (kind === "Section") {
    if (raw.source_span !== null) exactNested(raw.source_span, ["start_byte", "end_byte"], "section.source_span");
    if (raw.managed !== true || raw.marker_present !== true || raw.identity_status !== "canonical") {
      throw new TypeError("section managed, marker_present, and identity_status must use the canonical values");
    }
  }
  if (kind === "SSpecScenario" || kind === "SourceSymbol" || kind === "Test") sourceLocationShape(raw.source_location, `${kind} source_location`);
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
  assertNodeNestedShape(raw, kind);
  if (kind === "Artifact") {
    plainDataObject(raw, ARTIFACT_FIELDS, "artifact");
    const record = createArtifactRecord(raw);
    if (record.identity_status !== "canonical") throw new TypeError("trace inventory artifacts must have canonical identity");
    return { kind, record };
  }
  if (kind === "Section") return { kind, record: createSectionRecord(plainDataObject(raw, SECTION_FIELDS, "section")) };
  if (kind === "Requirement" || kind === "NFR") return { kind, record: createRequirementRecord(plainDataObject(raw, REQUIREMENT_FIELDS, "requirement")) };
  if (kind === "SSpecScenario") return { kind, record: createSSpecScenarioRecord(plainDataObject(raw, SCENARIO_FIELDS, "sspec scenario")) };
  if (kind === "SourceSymbol") return { kind, record: createSourceSymbolRecord(plainDataObject(raw, SYMBOL_FIELDS, "source symbol")) };
  return { kind, record: createTestRecord(plainDataObject(raw, TEST_FIELDS, "test")) };
}

function ownerArtifactUid(node) {
  if (node.kind === "Artifact") return node.record.uid;
  if (node.kind === "Section" || node.kind === "Requirement" || node.kind === "NFR" || node.kind === "SSpecScenario" || node.kind === "Test") return node.record.artifact_uid;
  if (node.kind === "SourceSymbol") return node.record.source_location.source_artifact_uid;
  throw new TypeError("unsupported trace node kind");
}

function requireNode(nodes, uid, kinds, name) {
  const node = nodes.get(uid);
  if (!node || !kinds.includes(node.kind)) throw new TypeError(`${name} must name a present ${kinds.join(" or ")} node`);
  return node;
}

function assertNodeScope(node, header, nodes) {
  const artifact = requireNode(nodes, ownerArtifactUid(node), ["Artifact"], `trace node ${node.record.uid} source artifact`);
  if (artifact.record.project_uid !== header.project_uid || artifact.record.revision !== header.revision_id) {
    throw new TypeError("trace source artifact must belong to the inventory project and revision");
  }
  if (node.kind !== "Artifact" && node.kind !== "Section" && (node.record.project_uid !== header.project_uid || node.record.revision_id !== header.revision_id)) {
    throw new TypeError("trace node must belong to the inventory project and revision");
  }
  if (node.kind === "Section" && node.record.artifact_uid !== artifact.record.uid) throw new TypeError("section source artifact must match artifact_uid");
  if (node.kind === "Requirement" || node.kind === "NFR") {
    const section = requireNode(nodes, node.record.section_uid, ["Section"], "requirement section_uid");
    if (section.record.artifact_uid !== node.record.artifact_uid) throw new TypeError("requirement section must belong to its source artifact");
  }
  if (node.kind === "SSpecScenario") for (const uid of node.record.requirement_uids) requireNode(nodes, uid, ["Requirement", "NFR"], "scenario requirement_uids entry");
  if (node.kind === "SourceSymbol") for (const uid of node.record.annotation_uids) requireNode(nodes, uid, ["Requirement", "NFR", "SSpecScenario"], "symbol annotation_uids entry");
  if (node.kind === "Test") {
    if (node.record.scenario_uid !== null) requireNode(nodes, node.record.scenario_uid, ["SSpecScenario"], "test scenario_uid");
    for (const uid of node.record.verifies_uids) requireNode(nodes, uid, ["Requirement", "NFR", "SSpecScenario", "SourceSymbol"], "test verifies_uids entry");
  }
}

function endpointAllowed(edgeType, fromKind, toKind) {
  const requirement = toKind === "Requirement" || toKind === "NFR";
  if (edgeType === "evidence_for") return (fromKind === "Artifact" || fromKind === "Section") && requirement;
  if (edgeType === "satisfies") return (fromKind === "Artifact" || fromKind === "Section" || fromKind === "SourceSymbol") && requirement;
  if (edgeType === "specifies") return fromKind === "SSpecScenario" && requirement;
  if (edgeType === "implements") return fromKind === "SourceSymbol" && (requirement || toKind === "SSpecScenario");
  if (edgeType === "verifies") return fromKind === "Test" && (requirement || toKind === "SSpecScenario" || toKind === "SourceSymbol");
  return false;
}

function edgeSortKey(edge) {
  return `${edge.from_uid}\0${edge.edge_type}\0${edge.to_uid}\0${edge.source_uid}`;
}

function normalizeEdges(rawEdges, nodes) {
  let previous = null;
  const edges = [];
  for (const raw of rawEdges) {
    plainDataObject(raw, EDGE_FIELDS, "trace edge");
    const edge = {
      edge_type: normalizeEnum(raw.edge_type, TRACE_EDGE_TYPES_V1, "edge_type"),
      from_uid: assertCanonicalUid(raw.from_uid, "from_uid"),
      to_uid: assertCanonicalUid(raw.to_uid, "to_uid"),
      source_uid: assertCanonicalUid(raw.source_uid, "source_uid"),
      origin: normalizeEnum(raw.origin, TRACE_ORIGINS_V1, "origin"),
      asserted_status: normalizeEnum(raw.asserted_status, TRACE_ASSERTED_STATUSES_V1, "asserted_status")
    };
    const key = edgeSortKey(edge);
    if (previous !== null && compareLexical(previous, key) >= 0) throw new TypeError("trace edges must be strictly sorted; duplicate semantic occurrences are forbidden");
    previous = key;
    const from = requireNode(nodes, edge.from_uid, TRACE_NODE_TYPES_V1, "trace edge from_uid");
    const to = requireNode(nodes, edge.to_uid, TRACE_NODE_TYPES_V1, "trace edge to_uid");
    requireNode(nodes, edge.source_uid, TRACE_NODE_TYPES_V1, "trace edge source_uid");
    if (edge.from_uid === edge.to_uid) throw new TypeError("trace edges must not be self edges");
    if (!endpointAllowed(edge.edge_type, from.kind, to.kind)) throw new TypeError("trace edge endpoint types are not allowed by the closed vocabulary");
    if (edge.asserted_status === "accepted" && !["explicit", "generated"].includes(edge.origin)) {
      throw new TypeError("inferred trace links cannot be asserted accepted");
    }
    edges.push(immutableRecord({ ...edge, declaration_status: "declared", strict_result: STRICT_UNAVAILABLE_V1 }));
  }
  return edges;
}

/** Validate bounded supplied facts and return a deterministic immutable view. */
export function createTraceInventoryV1(input) {
  plainDataObject(input, INVENTORY_FIELDS, "TraceInventoryV1 input");
  denseArray(input.nodes, "nodes");
  denseArray(input.edges, "edges");
  if (input.nodes.length > MAX_TRACE_INVENTORY_NODES_V1) throw new RangeError("trace node limit exceeded");
  if (input.edges.length > MAX_TRACE_INVENTORY_EDGES_V1) throw new RangeError("trace edge limit exceeded");
  assertClosedJson(input, "TraceInventoryV1 input", { items: 0, bytes: 0 });
  if (!isRecursivelyFrozen(input)) throw new TypeError("TraceInventoryV1 input must be recursively frozen");
  const header = {
    snapshot_uid: assertCanonicalUid(input.snapshot_uid, "snapshot_uid", ["V"]),
    project_uid: assertCanonicalUid(input.project_uid, "project_uid", ["P"]),
    revision_id: normalizeRevision(input.revision_id, "revision_id")
  };
  const nodes = new Map();
  let previous = null;
  for (const raw of input.nodes) {
    const node = normalizeNode(raw);
    if (previous !== null && compareLexical(previous, node.record.uid) >= 0) throw new TypeError("trace nodes must be strictly sorted and unique by uid");
    previous = node.record.uid;
    nodes.set(node.record.uid, node);
  }
  for (const node of nodes.values()) assertNodeScope(node, header, nodes);
  const edges = normalizeEdges(input.edges, nodes);
  const requirementRows = [...nodes.values()]
    .filter((node) => node.kind === "Requirement" || node.kind === "NFR")
    .map((node) => immutableRecord({
      requirement_uid: node.record.uid,
      requirement_type: node.kind,
      declared_edges: edges.filter((edge) => edge.from_uid === node.record.uid || edge.to_uid === node.record.uid),
      strict_result: STRICT_UNAVAILABLE_V1
    }));
  return immutableRecord({
    type: "TraceInventoryV1", ...header,
    nodes: [...nodes.values()].map((node) => immutableRecord({ node_type: node.kind, ...node.record })),
    edges, requirement_rows: requirementRows, strict_result: STRICT_UNAVAILABLE_V1
  });
}

export const TraceInventoryV1 = createTraceInventoryV1;
