import {
  assertUid,
  isProvisionalArtifactUid,
  compareLexical,
  immutableRecord,
  normalizeEnum,
  normalizeRevision,
  normalizeText,
  requireInteger,
  sortedUnique
} from "./identity.js";

export const EDGE_TYPES = Object.freeze([
  "contains", "classifies", "evidence_for", "derives", "satisfies", "realizes",
  "schedules", "specifies", "implements", "verifies", "covers", "produces",
  "links_to", "aliases", "supersedes", "extends", "promoted_from", "depends_on",
  "mounted_as"
]);
export const EDGE_ORIGINS = Object.freeze([
  "explicit", "generated", "structural", "lexical_inference", "semantic_inference", "llm_inference"
]);
export const EDGE_STATUSES = Object.freeze(["accepted", "proposed", "rejected", "stale", "superseded"]);

function generatorInfo(value) {
  if (value == null) return null;
  if (!value || typeof value !== "object" || Array.isArray(value)) throw new TypeError("generator must be an object");
  const record = {
    id: normalizeText(value.id, "generator.id"),
    version: normalizeText(String(value.version), "generator.version"),
    rule: normalizeText(value.rule, "generator.rule"),
    input_snapshot: normalizeText(value.input_snapshot, "generator.input_snapshot")
  };
  return immutableRecord(record);
}

export function createEdgeRecord(input) {
  if (!input || typeof input !== "object" || Array.isArray(input)) throw new TypeError("edge must be an object");
  const confidence = requireInteger(input.confidence_milli ?? 0, "confidence_milli", { min: 0, max: 1000 });
  const origin = normalizeEnum(input.origin, EDGE_ORIGINS, "origin");
  const record = {
    type: "edge",
    uid: assertUid(input.uid, "uid", ["E"]),
    edge_type: normalizeEnum(input.edge_type ?? input.relation ?? input.kind, EDGE_TYPES, "edge_type"),
    from_uid: assertUid(input.from_uid ?? input.from, "from_uid"),
    to_uid: assertUid(input.to_uid ?? input.to, "to_uid"),
    origin,
    status: normalizeEnum(input.status ?? "proposed", EDGE_STATUSES, "status"),
    confidence_milli: confidence,
    created_by: normalizeText(input.created_by ?? "system", "created_by"),
    created_at_revision: normalizeRevision(input.created_at_revision, "created_at_revision"),
    evidence_uids: sortedUnique(input.evidence_uids, "evidence_uids", (item) => assertUid(item, "evidence_uid")),
    generator: generatorInfo(input.generator)
  };
  if (record.from_uid === record.to_uid && record.edge_type !== "links_to") {
    throw new TypeError("an edge cannot connect a node to itself");
  }
  if (origin === "generated" && record.generator == null) {
    throw new TypeError("generated edges require generator metadata");
  }
  if (origin !== "generated" && record.generator != null) {
    throw new TypeError("only generated edges may carry generator metadata");
  }
  if (record.status === "accepted" && (isProvisionalArtifactUid(record.from_uid) || isProvisionalArtifactUid(record.to_uid))) {
    throw new TypeError("accepted trace edges cannot target provisional identity");
  }
  return immutableRecord(record);
}

export function isStrictEvidence(edge) {
  return edge?.type === "edge" && edge.status === "accepted" &&
    !isProvisionalArtifactUid(edge.from_uid) && !isProvisionalArtifactUid(edge.to_uid) &&
    (edge.origin === "explicit" || edge.origin === "generated");
}

export function edgeSortKey(edge) {
  return `${edge.from_uid}\u0000${edge.edge_type}\u0000${edge.to_uid}\u0000${edge.uid}`;
}

export function sortEdges(edges) {
  if (!Array.isArray(edges)) throw new TypeError("edges must be an array");
  return [...edges].sort((left, right) => compareLexical(edgeSortKey(left), edgeSortKey(right)));
}

export function inverseEdgeType(edgeType) {
  normalizeEnum(edgeType, EDGE_TYPES, "edge_type");
  return Object.freeze({ type: "inverse", of: edgeType });
}

export const TraceEdge = createEdgeRecord;
