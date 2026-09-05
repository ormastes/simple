import { contentHash, assertCanonicalUid, compareLexical, deepFreeze, normalizeHash } from "../model/identity.js";
import { ARTIFACT_KINDS, ARTIFACT_STATUSES } from "../model/artifact.js";
import { VIEW_KINDS, collisionAwareFilenames, createProjectionRecord, virtualSlug } from "../model/view.js";

/**
 * Pure Wave 5 projection kernel.  It deliberately accepts an already-built
 * immutable inventory: opening snapshots, authorizing reads, cursor signing,
 * MCP routing, and materialization are separate adapters.
 */
const EXPOSED_VIEWS = Object.freeze(["lifecycle", "feature", "component", "layer", "project", "status"]);
const MAX_PAGE_SIZE = 100;
const MAX_CURSOR_BYTES = 4096;
const CONTROL = /[\u0000-\u001f\u007f]/;
const SEGMENT = /^[A-Za-z0-9][A-Za-z0-9._-]*$/;
const WINDOWS_DEVICE = /^(?:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?$/i;

export class ProjectionUriError extends TypeError {
  constructor(code, message) {
    super(message);
    this.name = "ProjectionUriError";
    this.code = code;
  }
}

function uriFail(code, message) { throw new ProjectionUriError(code, message); }

function immutable(value) { return deepFreeze(value); }

function exactUid(value, prefix, field) {
  try { return assertCanonicalUid(value, field, [prefix]); }
  catch { uriFail("SPKURI004", `${field} must be a canonical ${prefix} UID`); }
}

function safeSegment(raw, field) {
  if (typeof raw !== "string" || raw.length === 0) uriFail("SPKURI005", `${field} must not be empty`);
  if (raw.normalize("NFC") !== raw || CONTROL.test(raw) || raw.includes("\\") || raw.includes("%")) {
    uriFail("SPKURI006", `${field} is not canonical`);
  }
  if (!SEGMENT.test(raw) || raw === "." || raw === ".." || WINDOWS_DEVICE.test(raw) || raw.endsWith(".") || raw.endsWith(" ")) {
    uriFail("SPKURI007", `${field} is not a safe canonical segment`);
  }
  return raw;
}

function checkedPath(path) {
  if (path === "/") return [];
  if (!path.startsWith("/") || path.endsWith("/") || path.includes("//")) uriFail("SPKURI008", "URI path is not canonical");
  return path.slice(1).split("/").map((part, index) => safeSegment(part, `path segment ${index}`));
}

/** Parse only canonical SPipe resource URIs; no URL normalization is allowed. */
export function parseCanonicalSpiceUri(uri) {
  if (typeof uri !== "string" || uri.length === 0 || uri.length > 8192) uriFail("SPKURI001", "URI must be a bounded string");
  if (uri.normalize("NFC") !== uri || CONTROL.test(uri) || uri.includes("\\") || uri.includes("%") || uri.includes("?") || uri.includes("#")) {
    uriFail("SPKURI002", "URI contains a forbidden noncanonical encoding or delimiter");
  }
  const match = /^spipe:\/\/([^/]+)(\/.*)?$/.exec(uri);
  if (!match) uriFail("SPKURI003", "URI must use canonical spipe:// authority syntax");
  const authority = match[1];
  const path = match[2] ?? "";
  if (authority !== "workspace" && authority !== "project") uriFail("SPKURI003", "URI authority is unsupported");
  const rootMatch = authority === "workspace" ? /^\/([^/]+)\/$/.exec(path) : null;
  const viewRootMatch = authority === "workspace" ? /^\/([^/]+)\/view\/([^/]+)\/$/.exec(path) : null;
  const parts = rootMatch ? [safeSegment(rootMatch[1], "workspace_uid")]
    : viewRootMatch ? [safeSegment(viewRootMatch[1], "workspace_uid"), "view", safeSegment(viewRootMatch[2], "view_kind")]
      : checkedPath(path);
  if (authority === "workspace") {
    if (rootMatch) return immutable({ family: "workspace_root", workspace_uid: exactUid(parts[0], "W", "workspace_uid"), uri });
    // The authority is workspace, so its first path component is always its UID.
    if (parts.length === 0) uriFail("SPKURI003", "workspace URI requires a UID and trailing slash");
    const workspace_uid = exactUid(parts[0], "W", "workspace_uid");
    if (parts.length === 1) uriFail("SPKURI003", "workspace root requires a trailing slash");
    if (parts[1] === "diagnostics" && parts.length === 2) return immutable({ family: "diagnostics", workspace_uid, uri });
    if (parts[1] === "trace" && parts.length === 3) return immutable({ family: "trace", workspace_uid, artifact_uid: exactUid(parts[2], "A", "artifact_uid"), uri });
    if (parts[1] !== "view" || parts.length < 3) uriFail("SPKURI003", "workspace URI family is unsupported");
    const view_kind = parts[2];
    if (!VIEW_KINDS.includes(view_kind)) uriFail("SPKURI009", "view kind is unsupported");
    if (parts.length === 3 && !viewRootMatch) uriFail("SPKURI003", "view root requires a trailing slash");
    return immutable({ family: "view", workspace_uid, view_kind, segments: parts.slice(3), uri });
  }
  if (parts.length !== 3) uriFail("SPKURI003", "project URI has an invalid shape");
  const project_uid = exactUid(parts[0], "P", "project_uid");
  if (parts[1] === "artifact") return immutable({ family: "artifact", project_uid, artifact_uid: exactUid(parts[2], "A", "artifact_uid"), uri });
  if (parts[1] === "section") return immutable({ family: "section", project_uid, section_uid: exactUid(parts[2], "S", "section_uid"), uri });
  uriFail("SPKURI003", "project URI family is unsupported");
}

function isRecursivelyFrozen(value, seen = new Set()) {
  if (!value || typeof value !== "object" || seen.has(value)) return true;
  if (!Object.isFrozen(value)) return false;
  seen.add(value);
  return Object.values(value).every((child) => isRecursivelyFrozen(child, seen));
}

function snapshotOf(inventory) {
  const snapshot = inventory?.snapshot;
  if (!snapshot || typeof snapshot.snapshot_uid !== "string" || !/^spks1-[a-f0-9]{64}$/.test(snapshot.snapshot_uid)) {
    throw new TypeError("projection kernel requires an immutable inventory snapshot");
  }
  if (!Array.isArray(inventory.artifacts) || !isRecursivelyFrozen(inventory)) throw new TypeError("projection kernel requires a recursively frozen inventory");
  return snapshot;
}

function pageSize(value, fallback) {
  const result = value ?? fallback;
  if (!Number.isSafeInteger(result) || result < 1 || result > MAX_PAGE_SIZE) throw new RangeError(`page size must be in 1..${MAX_PAGE_SIZE}`);
  return result;
}

function classificationKeys(artifacts, kind) {
  const values = kind === "lifecycle" ? artifacts.map(({ kind: value }) => value)
    : kind === "status" ? artifacts.map(({ status }) => status)
      : kind === "project" ? artifacts.map(({ project_uid }) => project_uid)
        : artifacts.flatMap((artifact) => artifact[`${kind}s`] ?? []);
  return [...new Set(values)].sort(compareLexical);
}

function directoryEntries(artifacts, kind, selector) {
  if (selector == null) return classificationKeys(artifacts, kind).map((key) => ({ type: "directory", key, title: key }));
  const filtered = artifacts.filter((artifact) => {
    if (kind === "lifecycle") return artifact.kind === selector;
    if (kind === "status") return artifact.status === selector;
    if (kind === "project") return artifact.project_uid === selector;
    return artifact[`${kind}s`].includes(selector);
  });
  const filenames = collisionAwareFilenames(filtered);
  return filtered.map((artifact) => ({
    type: "artifact", uid: artifact.uid, canonical_path: artifact.canonical_path,
    title: artifact.title, kind: artifact.kind, filename: filenames.get(artifact.uid)
  })).sort((left, right) => compareLexical(`${virtualSlug(left.title)}\0${left.kind}\0${left.uid}`, `${virtualSlug(right.title)}\0${right.kind}\0${right.uid}`));
}

function logicalPath(view_kind, segments) { return ["view", view_kind, ...segments].join("/"); }

function cursorEncode(value) { return Buffer.from(JSON.stringify(value), "utf8").toString("base64url"); }
function cursorDecode(cursor) {
  if (typeof cursor !== "string" || cursor.length === 0 || Buffer.byteLength(cursor, "utf8") > MAX_CURSOR_BYTES || !/^[A-Za-z0-9_-]+$/.test(cursor)) {
    throw new TypeError("cursor is malformed");
  }
  let value;
  try { value = JSON.parse(Buffer.from(cursor, "base64url").toString("utf8")); } catch { throw new TypeError("cursor is malformed"); }
  if (!value || Object.keys(value).sort().join(",") !== "after,limit,path,scope,snapshot,view,workspace") throw new TypeError("cursor is malformed");
  for (const field of ["workspace", "snapshot", "scope", "view", "path", "after"]) if (typeof value[field] !== "string") throw new TypeError("cursor is malformed");
  pageSize(value.limit);
  return value;
}

function projection({ workspace_uid, snapshot_id, view_kind, logical_path, scope_hash, page_start_key }) {
  return createProjectionRecord({ workspace_uid, snapshot_id, view_kind, logical_path, entry_kind: "directory", parameters_hash: contentHash(`${view_kind}\n${logical_path}`), auth_scope_hash: scope_hash, page_start_key: page_start_key === "" ? null : page_start_key });
}

export class ProjectionKernel {
  #workspaceUid; #inventory; #snapshot; #scopeHash; #pageSize;

  constructor({ workspace_uid, inventory, auth_scope_hash, page_size = MAX_PAGE_SIZE } = {}) {
    this.#workspaceUid = assertCanonicalUid(workspace_uid, "workspace_uid", ["W"]);
    this.#inventory = inventory;
    this.#snapshot = snapshotOf(inventory);
    this.#scopeHash = normalizeHash(auth_scope_hash, "auth_scope_hash");
    this.#pageSize = pageSize(page_size);
    Object.freeze(this);
  }

  list(uri, { cursor = null, limit = this.#pageSize } = {}) {
    const parsed = parseCanonicalSpiceUri(uri);
    if (parsed.family !== "view" || !EXPOSED_VIEWS.includes(parsed.view_kind) || parsed.workspace_uid !== this.#workspaceUid) throw new TypeError("projection URI is unsupported by the read-only kernel");
    if (parsed.segments.length > 1) throw new TypeError("projection URI is unsupported by the read-only kernel");
    const requestedLimit = pageSize(limit, this.#pageSize);
    const selector = parsed.segments[0] ?? null;
    if (selector != null && parsed.view_kind === "lifecycle" && !ARTIFACT_KINDS.includes(selector)) throw new TypeError("lifecycle selector is unsupported");
    if (selector != null && parsed.view_kind === "status" && !ARTIFACT_STATUSES.includes(selector)) throw new TypeError("status selector is unsupported");
    const path = logicalPath(parsed.view_kind, parsed.segments);
    let after = "";
    if (cursor !== null) {
      const decoded = cursorDecode(cursor);
      if (decoded.workspace !== this.#workspaceUid || decoded.snapshot !== this.#snapshot.snapshot_uid || decoded.scope !== this.#scopeHash || decoded.view !== parsed.view_kind || decoded.path !== path || decoded.limit !== requestedLimit) {
        throw new TypeError("cursor binding does not match this immutable projection");
      }
      after = decoded.after;
    }
    const entries = directoryEntries(this.#inventory.artifacts, parsed.view_kind, selector);
    const keyed = entries.map((entry) => ({ entry, key: entry.type === "artifact" ? entry.filename : entry.key }));
    const start = after === "" ? 0 : keyed.findIndex(({ key }) => key === after) + 1;
    if (after !== "" && start === 0) throw new TypeError("cursor position is not valid for this projection");
    const page = keyed.slice(start, start + requestedLimit);
    const next = start + requestedLimit < keyed.length
      ? cursorEncode({ workspace: this.#workspaceUid, snapshot: this.#snapshot.snapshot_uid, scope: this.#scopeHash, view: parsed.view_kind, path, limit: requestedLimit, after: page.at(-1).key }) : null;
    const record = projection({ workspace_uid: this.#workspaceUid, snapshot_id: this.#snapshot.snapshot_uid, view_kind: parsed.view_kind, logical_path: path, scope_hash: this.#scopeHash, page_start_key: after });
    return immutable({ type: "projection_page", uri: parsed.uri, snapshot_uid: this.#snapshot.snapshot_uid, projection: record, entries: page.map(({ entry }) => entry), next_cursor: next, exhausted: next === null });
  }

  read(uri) {
    const parsed = parseCanonicalSpiceUri(uri);
    if (parsed.family !== "view" || !EXPOSED_VIEWS.includes(parsed.view_kind) || parsed.workspace_uid !== this.#workspaceUid || parsed.segments.length !== 2) {
      throw new TypeError("projection URI is unsupported by the read-only kernel");
    }
    const [selector, filename] = parsed.segments;
    const entry = directoryEntries(this.#inventory.artifacts, parsed.view_kind, selector).find((candidate) => candidate.type === "artifact" && candidate.filename === filename);
    if (!entry) throw new TypeError("projection document does not exist");
    const content = ["<!-- generated by SPipe; do not edit -->", `<!-- canonical-uid: ${entry.uid} -->`, `<!-- canonical-path: ${entry.canonical_path} -->`, `<!-- snapshot: ${this.#snapshot.snapshot_uid} -->`, "", `# ${entry.title}`, "", `Kind: ${entry.kind}`].join("\n") + "\n";
    return immutable({ type: "projection_document", uri: parsed.uri, snapshot_uid: this.#snapshot.snapshot_uid, canonical_uid: entry.uid, canonical_path: entry.canonical_path, mime_type: "text/markdown", content });
  }

  write() { throw new TypeError("virtual projections are read-only"); }
}

export const ProjectionKernelV1 = ProjectionKernel;
