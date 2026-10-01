import { assertCanonicalUid, createProjectionUid, sha256 } from "../model/identity.js";
import { VIEW_KINDS } from "../model/view.js";
import { immutableRecord, normalizeText } from "../model/identity.js";

const DECODER = new TextDecoder("utf-8", { fatal: true });
const SAFE_SEGMENT = /^[\p{L}\p{N}][\p{L}\p{N}._-]*$/u;
const HEX = /^[0-9A-Fa-f]{2}$/;
const WINDOWS_DEVICE_BASENAME = /^(?:CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])$/i;

export class SpipeUriError extends TypeError {
  constructor(code, message) {
    super(message);
    this.name = "SpipeUriError";
    this.code = code;
  }
}

function fail(code, message) {
  throw new SpipeUriError(code, message);
}

function hasUnpairedSurrogate(value) {
  for (let index = 0; index < value.length; index += 1) {
    const unit = value.charCodeAt(index);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = value.charCodeAt(index + 1);
      if (next < 0xdc00 || next > 0xdfff) return true;
      index += 1;
    } else if (unit >= 0xdc00 && unit <= 0xdfff) return true;
  }
  return false;
}

function decodeOnce(value, field) {
  const bytes = [];
  let text = "";
  const flush = () => {
    if (!bytes.length) return;
    try { text += DECODER.decode(Uint8Array.from(bytes)); }
    catch { fail("SPK101", `${field} is not well-formed UTF-8`); }
    bytes.length = 0;
  };
  for (let index = 0; index < value.length; index += 1) {
    const character = value[index];
    if (character !== "%") {
      flush();
      text += character;
      continue;
    }
    const encoded = value.slice(index + 1, index + 3);
    if (!HEX.test(encoded)) fail("SPK101", `${field} has a malformed percent escape`);
    bytes.push(Number.parseInt(encoded, 16));
    index += 2;
  }
  flush();
  return text;
}

function rejectSecondDecodeHazard(value, field) {
  for (let index = 0; index < value.length; index += 1) {
    if (value[index] !== "%") continue;
    const encoded = value.slice(index + 1, index + 3);
    if (HEX.test(encoded) && "/\\.\u0000:".includes(String.fromCharCode(Number.parseInt(encoded, 16)))) {
      fail("SPK101", `${field} contains a second-decode path hazard`);
    }
  }
}

function normalizeSegment(raw, field) {
  const value = decodeOnce(raw, field).normalize("NFC");
  rejectSecondDecodeHazard(value, field);
  if (!value || /[\u0000-\u001f\u007f]/u.test(value)) fail("SPK101", `${field} is empty or contains a control character`);
  if (value === "." || value === ".." || value.includes("/") || value.includes("\\") || value.includes(":")) {
    fail("SPK101", `${field} is not a safe URI segment`);
  }
  if (value.endsWith(".") || value.endsWith(" ") || /^[A-Za-z]:/.test(value) || /^(?:\\\\|\\[?.])/u.test(value)) {
    fail("SPK101", `${field} is not portable across host filesystems`);
  }
  if (WINDOWS_DEVICE_BASENAME.test(value.split(".", 1)[0])) fail("SPK101", `${field} is a Windows reserved device name`);
  if (!SAFE_SEGMENT.test(value)) fail("SPK101", `${field} has unsupported characters`);
  return value;
}

function canonicalSegment(value) {
  return encodeURIComponent(value).replace(/%[0-9a-f]{2}/g, (escape) => escape.toUpperCase());
}

function parseQuery(raw, resourceType) {
  if (Buffer.byteLength(raw, "utf8") > 4096) fail("SPK101", "query exceeds the 4 KiB limit");
  if (!raw) return immutableRecord({});
  // Pagination and filtering are explicit tool parameters in the first slice.
  // No URI family has a query grammar yet, so accepting one would create a
  // second spelling with undeclared cache/authorization semantics.
  fail("SPK101", `${resourceType} URI does not permit query parameters`);
}

function canonicalQuery(parameters) {
  const pairs = Object.entries(parameters).map(([key, value]) => `${canonicalSegment(key)}=${canonicalSegment(value)}`);
  return pairs.length ? `?${pairs.join("&")}` : "";
}

/**
 * Parse a read-only SPipe resource URI without consulting the filesystem.
 * It deliberately validates raw components before any URL implementation can
 * normalize dot segments or collapse duplicated separators.
 */
export function parseSpipeUri(input) {
  if (typeof input !== "string" || input.length === 0 || hasUnpairedSurrogate(input) || Buffer.byteLength(input, "utf8") > 8192) {
    fail("SPK101", "URI must be a bounded well-formed UTF-8 string");
  }
  if (!input.startsWith("spipe://")) fail("SPK101", "URI must use the spipe scheme");
  if (input.includes("#")) fail("SPK101", "SPipe resources do not support fragments");
  const withoutScheme = input.slice("spipe://".length);
  const queryIndex = withoutScheme.indexOf("?");
  const authorityAndPath = queryIndex < 0 ? withoutScheme : withoutScheme.slice(0, queryIndex);
  const rawQuery = queryIndex < 0 ? "" : withoutScheme.slice(queryIndex + 1);
  const slash = authorityAndPath.indexOf("/");
  const authority = slash < 0 ? authorityAndPath : authorityAndPath.slice(0, slash);
  const rawPath = slash < 0 ? "" : authorityAndPath.slice(slash + 1);
  if (!authority || authority.includes("@") || authority.includes(":")) fail("SPK101", "SPipe URI authority is invalid");
  // The canonical workspace-root spelling ends in `/`; that slash denotes the
  // directory itself, not an empty child. Empty components elsewhere remain
  // ambiguous and are rejected before any filesystem or projection lookup.
  const rawSegments = rawPath === "" ? [] : rawPath.split("/");
  if (authority === "workspace" && rawSegments.length === 2 && rawSegments[1] === "") rawSegments.pop();
  if (rawSegments.some((segment) => segment === "")) fail("SPK101", "SPipe URI has an empty path segment");
  const segments = rawSegments.map((segment, index) => normalizeSegment(segment, `path segment ${index}`));

  let target;
  if (authority === "workspace") {
    if (segments.length === 1) target = { type: "workspace_directory", workspace: segments[0] };
    else if (segments.length >= 4 && segments[1] === "view" && VIEW_KINDS.includes(segments[2])) {
      target = { type: "view", workspace: segments[0], view_kind: segments[2], logical_path: [segments[2], ...segments.slice(3)].join("/") };
    } else if (segments.length === 3 && segments[1] === "trace") {
      try { assertCanonicalUid(segments[2], "trace artifact UID", ["A"]); }
      catch { fail("SPK101", "trace URI has an invalid artifact UID"); }
      target = { type: "trace", workspace: segments[0], artifact_uid: segments[2] };
    } else if (segments.length === 2 && segments[1] === "diagnostics") {
      target = { type: "diagnostics", workspace: segments[0] };
    } else fail("SPK101", "URI is not a supported workspace resource");
  } else if (authority === "project") {
    if (segments.length !== 3 || !["artifact", "section"].includes(segments[1])) fail("SPK101", "URI is not a supported project resource");
    try { assertCanonicalUid(segments[2], `${segments[1]} URI UID`, [segments[1] === "artifact" ? "A" : "S"]); }
    catch { fail("SPK101", `${segments[1]} URI has an invalid UID kind`); }
    target = { type: segments[1], project: segments[0], uid: segments[2] };
  } else if (authority === "skill" && segments.length === 0) {
    target = { type: "legacy_skill" };
  } else fail("SPK101", "SPipe URI authority is unsupported");

  const parameters = parseQuery(rawQuery, target.type);

  const pathname = authority === "skill" ? "" : target.type === "workspace_directory"
    ? `/${canonicalSegment(target.workspace)}/`
    : `/${segments.map(canonicalSegment).join("/")}`;
  return immutableRecord({
    scheme: "spipe", authority, ...target, parameters,
    canonical_uri: `spipe://${authority}${pathname}${canonicalQuery(parameters)}`
  });
}

function aggregateCoordinates(target) {
  if (target.type === "view") return { view_kind: target.view_kind, logical_path: target.logical_path };
  if (target.type === "trace") return { view_kind: "trace", logical_path: `trace/${target.artifact_uid}` };
  if (target.type === "diagnostics") return { view_kind: "diagnostics", logical_path: "diagnostics" };
  if (target.type === "workspace_directory") return { view_kind: "lifecycle", logical_path: "workspace" };
  return null;
}

function requireResolutionPort(context) {
  if (!context || typeof context !== "object" || !context.resolution_port || typeof context.resolution_port !== "object") {
    fail("SPK101", "resource resolution requires a resolution port");
  }
  if (typeof context.revision_id !== "string" || context.revision_id.length === 0) fail("SPK101", "resource resolution requires a revision ID");
  return context.resolution_port;
}

function exactReceipt(value, fields, label) {
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype || Object.getOwnPropertySymbols(value).length !== 0) {
    fail("SPK101", `${label} receipt must be a plain closed record`);
  }
  const actual = Object.getOwnPropertyNames(value).sort();
  const expected = [...fields].sort();
  if (actual.length !== expected.length || actual.some((field, index) => field !== expected[index])) fail("SPK101", `${label} receipt has an invalid schema`);
  for (const field of fields) {
    const descriptor = Object.getOwnPropertyDescriptor(value, field);
    if (!descriptor || !Object.hasOwn(descriptor, "value") || descriptor.enumerable !== true) fail("SPK101", `${label} receipt must contain own data fields only`);
  }
  return value;
}

function authorizeWorkspace(target, context, port) {
  if (typeof port.resolveWorkspace !== "function") fail("SPK101", "resolution port cannot resolve workspaces");
  const receipt = exactReceipt(port.resolveWorkspace({ workspace: target.workspace, workspace_uid: context.workspace_uid, revision_id: context.revision_id, snapshot_id: context.snapshot_id }),
    ["authorized", "workspace", "workspace_uid", "revision_id", "snapshot_id"], "workspace");
  if (receipt.authorized !== true || receipt.workspace !== target.workspace || receipt.workspace_uid !== context.workspace_uid || receipt.revision_id !== context.revision_id || receipt.snapshot_id !== context.snapshot_id) {
    fail("SPK101", "workspace resolution is unauthorized or inconsistent");
  }
}

function authorizeProject(target, context, port) {
  if (typeof port.resolveProject !== "function") fail("SPK101", "resolution port cannot resolve projects");
  const receipt = exactReceipt(port.resolveProject({ project: target.project, uid: target.uid, kind: target.type, revision_id: context.revision_id, snapshot_id: context.snapshot_id }),
    ["authorized", "project", "canonical_uid", "kind", "revision_id", "snapshot_id"], "project");
  if (receipt.authorized !== true || receipt.project !== target.project || receipt.canonical_uid !== target.uid || receipt.kind !== target.type || receipt.revision_id !== context.revision_id || receipt.snapshot_id !== context.snapshot_id) {
    fail("SPK101", "project resolution is unauthorized or inconsistent");
  }
}

function authorizeLegacySkill(target, context, port) {
  if (typeof port.resolveLegacySkill !== "function") fail("SPK101", "resolution port cannot resolve the legacy skill alias");
  const receipt = exactReceipt(port.resolveLegacySkill({ uri: target.canonical_uri, revision_id: context.revision_id, snapshot_id: context.snapshot_id }),
    ["authorized", "uri", "project", "canonical_uid", "revision_id", "snapshot_id"], "legacy skill");
  try { assertCanonicalUid(receipt.canonical_uid, "legacy skill canonical UID", ["A"]); }
  catch { fail("SPK101", "legacy skill alias has an invalid canonical artifact UID"); }
  if (receipt.authorized !== true || receipt.uri !== target.canonical_uri || typeof receipt.project !== "string" || receipt.project.length === 0 || receipt.revision_id !== context.revision_id || receipt.snapshot_id !== context.snapshot_id) {
    fail("SPK101", "legacy skill alias is unauthorized or inconsistent");
  }
  return receipt;
}

/** Resolve a parsed URI to immutable identity data for one pinned snapshot. */
export function resolveVirtualResource(input, context) {
  if (typeof input !== "string") fail("SPK101", "resource resolution accepts a URI string only");
  const target = parseSpipeUri(input);
  const port = requireResolutionPort(context);
  const coordinates = aggregateCoordinates(target);
  if (!coordinates) {
    if (target.type === "legacy_skill") {
      const receipt = authorizeLegacySkill(target, context, port);
      return immutableRecord({ type: "legacy_skill", canonical_uri: target.canonical_uri, canonical_uid: receipt.canonical_uid, project: receipt.project, revision_id: context.revision_id, snapshot_id: context.snapshot_id, read_only: true });
    }
    const prefix = target.type === "artifact" ? "A" : "S";
    try { assertCanonicalUid(target.uid, `${target.type} URI UID`, [prefix]); }
    catch { fail("SPK101", `${target.type} URI has an invalid UID kind`); }
    authorizeProject(target, context, port);
    return immutableRecord({ type: target.type, canonical_uri: target.canonical_uri, canonical_uid: target.uid, project: target.project, revision_id: context.revision_id, snapshot_id: context.snapshot_id, read_only: true });
  }
  authorizeWorkspace(target, context, port);
  // Parameters are re-derived from the parsed URI, never caller supplied: a
  // caller cannot alias distinct query resources into one projection identity.
  const parametersHash = sha256({ parameters: target.parameters });
  const projectionUid = createProjectionUid({
    workspace_uid: context.workspace_uid,
    snapshot_id: context.snapshot_id,
    view_kind: coordinates.view_kind,
    normalized_logical_path: coordinates.logical_path,
    normalized_parameters_hash: parametersHash,
    effective_auth_scope_hash: context.auth_scope_hash,
    page_start_key: context.page_start_key ?? ""
  });
  return immutableRecord({
    type: target.type, canonical_uri: target.canonical_uri, read_only: true,
    projection_uid: projectionUid, snapshot_id: context.snapshot_id,
    workspace: target.workspace, view_kind: coordinates.view_kind,
    logical_path: coordinates.logical_path, parameters: target.parameters
  });
}

export const SpipeUri = parseSpipeUri;
