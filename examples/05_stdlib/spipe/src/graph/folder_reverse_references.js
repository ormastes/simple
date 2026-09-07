import { createHmac, randomBytes, timingSafeEqual } from "node:crypto";

import { compareLexical, normalizeCanonicalPath } from "../model/identity.js";
import { canonicalJson, freezeDeep } from "../storage/canonical.js";
import { compareEdges } from "./canonical.js";
import { GRAPH_LIMITS } from "./store.js";

const DEFAULT_LIMIT = 100;
const HARD_LIMIT = 1_000;

function fail(code, message) {
  const error = new Error(message);
  error.code = code;
  throw error;
}

function bounded(value, fallback, hard, field) {
  const selected = value ?? fallback;
  if (!Number.isSafeInteger(selected) || selected < 1 || selected > hard) {
    throw new RangeError(`${field} must be an integer between 1 and ${hard}`);
  }
  return selected;
}

/** Normalize a project-relative directory without weakening segment boundaries. */
export function normalizeFolderBoundary(value) {
  if (value === "" || value === ".") return "";
  if (typeof value !== "string" || value.includes("\\") || value.startsWith("/") || value.endsWith("/")) {
    throw new TypeError("folder_path must be a canonical project-relative directory");
  }
  const parts = value.split("/");
  if (parts.some((part) => part === "" || part === "." || part === "..")) {
    throw new TypeError("folder_path must be a canonical project-relative directory");
  }
  return value.normalize("NFC");
}

function isWithinFolder(path, folder) {
  return folder === "" || path.startsWith(`${folder}/`);
}

function sourceArtifactUid(edge, artifactPaths) {
  const located = edge.provenance?.source_location?.source_artifact_uid ?? null;
  if (located !== null && artifactPaths.has(located)) return located;
  return artifactPaths.has(edge.from_uid) ? edge.from_uid : null;
}

/**
 * Immutable, snapshot-bound reverse-reference query surface.
 *
 * References are attributed to their provenance source artifact.  An edge
 * without resolvable source ownership is excluded instead of being guessed
 * into a folder.  Results use canonical path + graph edge order.
 */
export class FolderReverseReferenceIndex {
  #snapshotUid;
  #graphRoot;
  #artifactPaths;
  #edges;
  #byTarget;
  #indexedTargetUid;
  #cursorKey;

  constructor({ snapshot_uid, graph_root, artifacts, edges, cursor_key = null, max_indexed_edges = GRAPH_LIMITS.returned_edges.hard, indexed_target_uid = null } = {}) {
    if (typeof snapshot_uid !== "string" || snapshot_uid.length === 0) throw new TypeError("snapshot_uid is required");
    if (typeof graph_root !== "string" || graph_root.length === 0) throw new TypeError("graph_root is required");
    if (!Array.isArray(artifacts) || !Array.isArray(edges)) throw new TypeError("artifacts and edges are required");
    const edgeLimit = bounded(max_indexed_edges, GRAPH_LIMITS.returned_edges.hard, GRAPH_LIMITS.returned_edges.hard, "max_indexed_edges");
    if (edges.length > edgeLimit) fail("SPK020", "reverse-reference index edge limit exceeded");

    const artifactPaths = new Map();
    for (const artifact of artifacts) {
      if (artifactPaths.has(artifact.uid)) fail("SPK001", `duplicate artifact UID: ${artifact.uid}`);
      artifactPaths.set(artifact.uid, normalizeCanonicalPath(artifact.canonical_path, "canonical_path"));
    }
    if (indexed_target_uid !== null && (typeof indexed_target_uid !== "string" || indexed_target_uid.length === 0)) {
      throw new TypeError("indexed_target_uid must be a non-empty string");
    }
    // Keep the immutable graph rows compact and materialize the substantially
    // larger path-attributed/sorted view only for targets that are queried.
    // CLI calls query one target and MCP sessions typically query a small
    // fraction of graph targets, so eagerly allocating every result item made
    // startup proportional to the entire graph's result cardinality.
    const indexedItems = [];
    for (const edge of edges) {
      if (indexed_target_uid !== null && edge.to_uid !== indexed_target_uid) continue;
      const ownerUid = sourceArtifactUid(edge, artifactPaths);
      // Match the eager index's ownership boundary: unresolved caller-owned
      // edges are excluded and must not be frozen as an incidental side effect.
      if (ownerUid === null) continue;
      freezeDeep(edge);
      if (indexed_target_uid !== null) indexedItems.push(freezeDeep({ edge, source_artifact_uid: ownerUid, source_path: artifactPaths.get(ownerUid) }));
    }
    this.#snapshotUid = snapshot_uid;
    this.#graphRoot = graph_root;
    this.#artifactPaths = artifactPaths;
    this.#edges = indexed_target_uid === null ? Object.freeze([...edges]) : Object.freeze([]);
    this.#byTarget = new Map();
    this.#indexedTargetUid = indexed_target_uid;
    if (indexed_target_uid !== null) {
      indexedItems.sort((left, right) => compareLexical(left.source_path, right.source_path) || compareEdges(left.edge, right.edge));
      this.#byTarget.set(indexed_target_uid, Object.freeze(indexedItems));
    }
    this.#cursorKey = cursor_key === null ? randomBytes(32) : Buffer.from(cursor_key);
    if (this.#cursorKey.length < 32) throw new TypeError("cursor_key must contain at least 32 bytes");
  }

  query({ target_uid, folder_path = "", limit = DEFAULT_LIMIT, max_work_units = GRAPH_LIMITS.work_units.default, cursor = null } = {}) {
    if (typeof target_uid !== "string" || target_uid.length === 0) throw new TypeError("target_uid is required");
    if (this.#indexedTargetUid !== null && target_uid !== this.#indexedTargetUid) {
      throw new TypeError("target_uid does not match the target-specific reverse-reference index");
    }
    const folder = normalizeFolderBoundary(folder_path);
    const pageLimit = bounded(limit, DEFAULT_LIMIT, HARD_LIMIT, "limit");
    const workLimit = bounded(max_work_units, GRAPH_LIMITS.work_units.default, GRAPH_LIMITS.work_units.hard, "max_work_units");
    const binding = { snapshot_uid: this.#snapshotUid, graph_root: this.#graphRoot, target_uid, folder_path: folder, limit: pageLimit, max_work_units: workLimit };
    let position = cursor === null ? 0 : this.#decodeCursor(cursor, binding);
    const candidates = this.#candidatesForTarget(target_uid);
    const items = [];
    let work = 0;
    while (position < candidates.length && items.length < pageLimit && work < workLimit) {
      const candidate = candidates[position];
      position += 1;
      work += 1;
      if (isWithinFolder(candidate.source_path, folder)) items.push(candidate);
    }
    const complete = position >= candidates.length;
    const reason = complete ? null : items.length >= pageLimit ? "limit" : "work_units";
    return freezeDeep({
      snapshot_uid: this.#snapshotUid, graph_root: this.#graphRoot,
      target_uid, folder_path: folder, items, complete, reason,
      counters: { returned_references: items.length, work_units: work },
      next_cursor: complete ? null : this.#encodeCursor({ ...binding, position })
    });
  }

  #candidatesForTarget(targetUid) {
    const cached = this.#byTarget.get(targetUid);
    if (cached !== undefined) return cached;
    const items = [];
    for (const edge of this.#edges) {
      if (edge.to_uid !== targetUid) continue;
      const ownerUid = sourceArtifactUid(edge, this.#artifactPaths);
      if (ownerUid === null) continue;
      items.push(freezeDeep({ edge, source_artifact_uid: ownerUid, source_path: this.#artifactPaths.get(ownerUid) }));
    }
    items.sort((left, right) => compareLexical(left.source_path, right.source_path) || compareEdges(left.edge, right.edge));
    Object.freeze(items);
    // An attacker may submit infinitely many absent target UIDs. Empty misses
    // are deliberately not retained; non-empty entries remain bounded by the
    // admitted edge limit because every cached target owns at least one edge.
    if (items.length !== 0) this.#byTarget.set(targetUid, items);
    return items;
  }

  #encodeCursor(record) {
    const payload = Buffer.from(canonicalJson(record), "utf8").toString("base64url");
    const signature = createHmac("sha256", this.#cursorKey).update(payload).digest("base64url");
    return `${payload}.${signature}`;
  }

  #decodeCursor(cursor, binding) {
    if (typeof cursor !== "string" || !cursor.includes(".")) fail("SPK704", "reverse-reference cursor is invalid");
    const [payload, signature, ...extra] = cursor.split(".");
    if (extra.length !== 0) fail("SPK704", "reverse-reference cursor is invalid");
    const expected = createHmac("sha256", this.#cursorKey).update(payload).digest();
    let actual;
    try { actual = Buffer.from(signature, "base64url"); } catch { fail("SPK704", "reverse-reference cursor is invalid"); }
    if (actual.length !== expected.length || !timingSafeEqual(actual, expected)) fail("SPK704", "reverse-reference cursor authentication failed");
    let record;
    try { record = JSON.parse(Buffer.from(payload, "base64url").toString("utf8")); } catch { fail("SPK704", "reverse-reference cursor payload is invalid"); }
    for (const [key, value] of Object.entries(binding)) {
      if (canonicalJson(record[key]) !== canonicalJson(value)) fail("SPK704", `reverse-reference cursor ${key} binding mismatch`);
    }
    if (!Number.isSafeInteger(record.position) || record.position < 0) fail("SPK704", "reverse-reference cursor position is invalid");
    return record.position;
  }
}

/** Build the public Wave 6 query surface from one immutable compiler result. */
export function createFolderReverseReferenceIndex(inventory, options = {}) {
  if (!inventory?.snapshot || !inventory?.graph || !Array.isArray(inventory.artifacts)) {
    throw new TypeError("compiled inventory is required");
  }
  return new FolderReverseReferenceIndex({
    snapshot_uid: inventory.snapshot.snapshot_uid,
    graph_root: inventory.graph.graph_root,
    artifacts: inventory.artifacts,
    edges: inventory.graph.edges,
    ...options
  });
}
