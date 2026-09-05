#!/usr/bin/env node
// Tracked GitHub-runner adapter for the pure-Simple v1 self-review policy.
// It is mutation-free and never submits or claims a GitHub provider approval.

import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";

const POLICY_HEADER_KEYS = ["schema", "default_allow", "max_ttl_seconds", "authority"];
const POLICY_RECORD_KEYS = [
  "schema", "record_id", "effect", "repository", "pull_request_number",
  "head_sha", "session_id", "self_reviewer", "changed_paths_manifest_sha256",
  "review_evidence_sha256", "allow_scopes", "deny_scopes", "issuer",
  "issued_at_unix", "expires_at_unix", "previous_record_sha256", "signature",
];
const REQUEST_KEYS = [
  "schema", "repository_provider", "repository_id", "repository_node_id", "repository",
  "pull_request_number", "head_sha", "session_id", "author_provider", "author_identity",
  "reviewer_provider", "reviewer_identity", "reviewer_model", "reviewer_tier",
  "reviewer_effort", "review_evidence_mode", "now_unix", "decision_expires_at_unix",
  "higher_model_verdict", "higher_model_p0_count", "higher_model_p1_count",
  "review_evidence_sha256", "expected_policy_db_sha256", "policy_db_authenticated",
  "changed_manifest_authenticated", "review_evidence_broker_authenticated",
  "self_attestation_authorized", "target_repository_id", "target_ref",
  "target_ruleset_id", "target_ruleset_version", "target_ruleset_sha256", "base_sha",
  "merge_base_sha", "diff_sha256", "strict_up_to_date", "protected_target",
  "provider_resolution_authenticated",
];
const ZERO_SHA256 = "0".repeat(64);

function sha256(value) {
  return createHash("sha256").update(value, "utf8").digest("hex");
}

// JSON.parse accepts duplicate object keys. The policy contract does not, so
// use a small strict parser that rejects duplicates before schema validation.
export function parseStrictJson(source) {
  let offset = 0;
  const fail = (message) => { throw new Error(`${message} at byte ${offset}`); };
  const whitespace = () => {
    while (offset < source.length && /[\x20\t\r\n]/.test(source[offset])) offset += 1;
  };
  const string = () => {
    if (source[offset] !== '"') fail("expected JSON string");
    const start = offset++;
    while (offset < source.length) {
      const char = source[offset++];
      if (char === '"') {
        try { return JSON.parse(source.slice(start, offset)); }
        catch { fail("malformed JSON string"); }
      }
      if (char === "\\") {
        if (offset >= source.length) fail("unterminated JSON escape");
        const escaped = source[offset++];
        if (escaped === "u") {
          if (!/^[0-9a-fA-F]{4}$/.test(source.slice(offset, offset + 4))) fail("malformed unicode escape");
          offset += 4;
        } else if (!'"\\/bfnrt'.includes(escaped)) {
          fail("malformed JSON escape");
        }
      } else if (char.charCodeAt(0) < 0x20) {
        fail("unescaped control character");
      }
    }
    fail("unterminated JSON string");
  };
  const value = () => {
    whitespace();
    if (source[offset] === "{") {
      offset += 1;
      const result = {};
      const seen = new Set();
      whitespace();
      if (source[offset] === "}") { offset += 1; return result; }
      while (true) {
        whitespace();
        const key = string();
        if (seen.has(key)) fail(`duplicate JSON key ${key}`);
        seen.add(key);
        whitespace();
        if (source[offset++] !== ":") fail("expected colon");
        result[key] = value();
        whitespace();
        const delimiter = source[offset++];
        if (delimiter === "}") return result;
        if (delimiter !== ",") fail("expected comma or object end");
      }
    }
    if (source[offset] === "[") {
      offset += 1;
      const result = [];
      whitespace();
      if (source[offset] === "]") { offset += 1; return result; }
      while (true) {
        result.push(value());
        whitespace();
        const delimiter = source[offset++];
        if (delimiter === "]") return result;
        if (delimiter !== ",") fail("expected comma or array end");
      }
    }
    if (source[offset] === '"') return string();
    for (const [literal, result] of [["true", true], ["false", false], ["null", null]]) {
      if (source.startsWith(literal, offset)) { offset += literal.length; return result; }
    }
    const match = source.slice(offset).match(/^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?/);
    if (!match) fail("expected JSON value");
    offset += match[0].length;
    const number = Number(match[0]);
    if (!Number.isFinite(number)) fail("non-finite JSON number");
    return number;
  };
  const result = value();
  whitespace();
  if (offset !== source.length) fail("trailing JSON content");
  return result;
}

function closedObject(value, keys) {
  if (value === null || Array.isArray(value) || typeof value !== "object") return false;
  const actual = Object.keys(value);
  return actual.length === keys.length && keys.every((key) => Object.hasOwn(value, key));
}

function integer(value) { return Number.isSafeInteger(value); }
function hex(value, length) { return typeof value === "string" && new RegExp(`^[0-9a-f]{${length}}$`).test(value); }
function sha256Valid(value) { return hex(value, 64); }
function commitShaValid(value) { return hex(value, 40) || hex(value, 64); }
function safeIdentity(value) {
  return typeof value === "string" && value.length > 0 && value.length <= 192 &&
    !value.includes("..") && /^[A-Za-z0-9._/:@-]+$/.test(value);
}
function safeRepository(value) {
  const parts = typeof value === "string" ? value.split("/") : [];
  return parts.length === 2 && parts.every(safeIdentity);
}
function safeRepoPath(value) {
  if (typeof value !== "string" || value === "" || value.startsWith("/") || value.endsWith("/") ||
      value.includes("\\") || value.includes("//") || value.includes("|") || value.includes('"') ||
      value !== value.trim() || !/^[A-Za-z0-9+,.\-\/@_]+$/.test(value)) return false;
  return value.split("/").every((part) => part !== "" && part !== "." && part !== ".." && part !== ".git");
}

function parseScopes(raw) {
  if (!Array.isArray(raw)) throw new Error("self-review scopes must be an array");
  const scopes = [];
  for (const scope of raw) {
    if (!closedObject(scope, ["kind", "path"])) throw new Error("self-review scope must be a closed kind/path object");
    if (!["code", "text", "file", "directory_files", "directory_recursive"].includes(scope.kind))
      throw new Error("self-review scope kind is unsupported");
    if (["code", "text"].includes(scope.kind) ? scope.path !== "" : !safeRepoPath(scope.path))
      throw new Error(["code", "text"].includes(scope.kind) ? "code/text self-review scope must not carry a path" : "path self-review scope is unsafe");
    if (scopes.some((item) => item.kind === scope.kind && item.path === scope.path))
      throw new Error("self-review scope is duplicated");
    scopes.push(scope);
  }
  return scopes;
}

function parsePolicyRecord(value, maxTtlSeconds) {
  if (!closedObject(value, POLICY_RECORD_KEYS)) throw new Error("self-review policy record is not a closed grant/1 object");
  if (value.schema !== "spipe-self-review-policy-db/grant/1") throw new Error("self-review policy record schema is unsupported");
  if (!closedObject(value.repository, ["provider", "id", "node_id", "name"])) throw new Error("self-review record repository identity is not closed");
  if (!closedObject(value.self_reviewer, ["provider", "identity", "model", "tier", "effort"])) throw new Error("self-review record reviewer identity is not closed");
  if (!closedObject(value.issuer, ["provider", "identity", "key_id"])) throw new Error("self-review record issuer identity is not closed");
  const allowScopes = parseScopes(value.allow_scopes);
  const denyScopes = parseScopes(value.deny_scopes);
  if (!safeIdentity(value.record_id) || !["deny", "constrain"].includes(value.effect)) throw new Error("self-review record id/effect is invalid");
  if (value.repository.provider !== "github" || !integer(value.repository.id) || value.repository.id <= 0 ||
      !safeIdentity(value.repository.node_id) || !safeRepository(value.repository.name)) throw new Error("self-review record repository identity is invalid");
  if (!integer(value.pull_request_number) || value.pull_request_number <= 0 || !commitShaValid(value.head_sha) || !safeIdentity(value.session_id))
    throw new Error("self-review record PR/head/session identity is invalid");
  if (![value.self_reviewer.provider, value.self_reviewer.identity, value.self_reviewer.model].every(safeIdentity))
    throw new Error("self-review record reviewer identity is invalid");
  if (value.self_reviewer.tier !== "high_capability" || !["high", "xhigh", "max", "ultra"].includes(value.self_reviewer.effort))
    throw new Error("self-review record requires a high-capability, high-effort reviewer");
  if (!sha256Valid(value.changed_paths_manifest_sha256) || !sha256Valid(value.review_evidence_sha256))
    throw new Error("self-review record receipt bindings are invalid");
  if (![value.issuer.provider, value.issuer.identity, value.issuer.key_id].every(safeIdentity)) throw new Error("self-review record issuer identity is invalid");
  if (![value.issued_at_unix, value.expires_at_unix].every(integer) || value.issued_at_unix <= 0 ||
      value.expires_at_unix <= value.issued_at_unix || value.expires_at_unix - value.issued_at_unix > maxTtlSeconds)
    throw new Error("self-review record time window is invalid");
  if (!sha256Valid(value.previous_record_sha256) || typeof value.signature !== "string" || value.signature.length < 32 || value.signature.length > 4096)
    throw new Error("self-review record hash-chain/signature fields are invalid");
  if (value.effect === "constrain" && allowScopes.length === 0) throw new Error("self-review constrain record must narrow to at least one allow scope");
  return { ...value, allow_scopes: allowScopes, deny_scopes: denyScopes };
}

export function parsePolicyDb(payload) {
  const digest = sha256(payload);
  try {
    const lines = payload.split("\n").map((line) => line.trim()).filter(Boolean);
    if (lines.length === 0) throw new Error("operator self-review policy database is empty");
    const header = parseStrictJson(lines[0]);
    if (!closedObject(header, POLICY_HEADER_KEYS)) throw new Error("self-review policy database header is malformed");
    if (header.schema !== "spipe-self-review-policy-db/1" || header.default_allow !== true || header.authority !== "operator_owned_external")
      throw new Error("self-review policy database header is not the default-allow external authority");
    if (!integer(header.max_ttl_seconds) || header.max_ttl_seconds <= 0 || header.max_ttl_seconds > 86400)
      throw new Error("self-review policy database maximum TTL must be within 24 hours");
    const records = [];
    let previous = ZERO_SHA256;
    for (const line of lines.slice(1)) {
      let raw;
      try { raw = parseStrictJson(line); } catch { throw new Error("self-review policy database JSONL record is malformed"); }
      const record = parsePolicyRecord(raw, header.max_ttl_seconds);
      if (record.previous_record_sha256 !== previous) throw new Error("self-review policy database hash chain is broken");
      if (records.some((existing) => existing.record_id === record.record_id)) throw new Error("self-review policy record id is duplicated");
      records.push(record);
      previous = sha256(line);
    }
    return { ...header, records, sha256: digest, valid: true, error: "" };
  } catch (error) {
    return { schema: "", default_allow: false, max_ttl_seconds: 0, authority: "", records: [], sha256: digest, valid: false, error: error.message };
  }
}

function emptyChange() {
  return { status: "", path: "", previous_path: "", content_kind: "", previous_content_kind: "", semantic_class: "", previous_semantic_class: "", file_type: "", previous_file_type: "", encoding: "", previous_encoding: "" };
}

function changeShapeError(change) {
  if (!safeRepoPath(change.path) || (change.previous_path !== "" && !safeRepoPath(change.previous_path))) return "changed-path manifest contains traversal, metadata, or non-canonical path syntax";
  if (change.status === "added") {
    if (change.previous_path !== "" || change.file_type !== "regular" || change.previous_file_type !== "absent" || change.previous_content_kind !== "absent" || change.previous_semantic_class !== "absent" || change.encoding !== "utf8" || change.previous_encoding !== "absent") return "added path has an invalid or unsafe shape";
  } else if (["modified", "mode_changed"].includes(change.status)) {
    if (change.previous_path !== "" || change.file_type !== "regular" || change.previous_file_type !== "regular" || change.encoding !== "utf8" || change.previous_encoding !== "utf8") return "modified path has an invalid or unsafe shape";
  } else if (change.status === "deleted") {
    if (change.previous_path !== "" || change.file_type !== "absent" || change.previous_file_type !== "regular" || change.content_kind !== "absent" || change.semantic_class !== "absent" || change.encoding !== "absent" || change.previous_encoding !== "utf8") return "deleted path has an invalid or unsafe shape";
  } else if (["renamed", "copied"].includes(change.status)) {
    if (change.previous_path === "" || change.previous_path === change.path || change.file_type !== "regular" || change.previous_file_type !== "regular" || change.encoding !== "utf8" || change.previous_encoding !== "utf8") return "rename/copy path has an invalid or unsafe shape";
  } else return `changed-path status is unsupported: ${change.status}`;
  return "";
}

export function parseChangedManifest(payload) {
  const invalid = (error) => ({ valid: false, error, sha256: sha256(payload), changes: [] });
  const globals = ["schema", "repository_provider", "repository_id", "repository_node_id", "repository", "pull_request_number", "head_sha", "base_repository_provider", "base_repository_id", "base_repository_node_id", "base_repository", "base_ref", "base_sha", "merge_base_sha", "diff_sha256"];
  const entries = ["path", "previous_path", "content_kind", "previous_content_kind", "semantic_class", "previous_semantic_class", "file_type", "previous_file_type", "encoding", "previous_encoding"];
  const manifest = { changes: [] };
  const globalSeen = new Set();
  let current = emptyChange();
  let inChange = false;
  let seen = new Set();
  for (const raw of payload.split("\n")) {
    if (raw.includes('"') || raw.endsWith(" ") || raw.endsWith("\t")) return invalid("changed-path manifest contains quoted or trailing-whitespace aliases");
    const line = raw.trim();
    if (line === "" || line.startsWith("#") || line === "changed_paths:" || line === "changes:") continue;
    const separator = line.indexOf(":");
    if (separator < 0) return invalid("malformed changed-path manifest field");
    const key = line.slice(0, separator);
    const rawValue = line.slice(separator + 1);
    if (rawValue.startsWith("  ")) return invalid("changed-path manifest contains leading-whitespace aliases");
    const value = rawValue.trim();
    if (globals.includes(key)) {
      if (inChange || globalSeen.has(key)) return invalid("changed-path global fields are duplicated or out of order");
      globalSeen.add(key);
      manifest[key] = ["repository_id", "pull_request_number", "base_repository_id"].includes(key) && /^[+-]?[0-9]+$/.test(value) ? Number(value) : value;
      continue;
    }
    if (line.startsWith("- status:")) {
      if (inChange) manifest.changes.push(current);
      current = emptyChange();
      current.status = value;
      inChange = true;
      seen = new Set(["status"]);
      continue;
    }
    if (!inChange || seen.has(key)) return invalid("changed-path entry field is duplicated or out of place");
    seen.add(key);
    if (!entries.includes(key)) return invalid(`unsupported changed-path entry field: ${key}`);
    current[key] = value;
  }
  if (inChange) manifest.changes.push(current);
  if (manifest.schema !== "spipe-changed-path-manifest/1" || manifest.repository_provider !== "github" ||
      !integer(manifest.repository_id) || manifest.repository_id <= 0 || !safeIdentity(manifest.repository_node_id) ||
      !safeRepository(manifest.repository) || !integer(manifest.pull_request_number) || manifest.pull_request_number <= 0 ||
      !commitShaValid(manifest.head_sha) || manifest.base_repository_provider !== "github" ||
      !integer(manifest.base_repository_id) || manifest.base_repository_id <= 0 || !safeIdentity(manifest.base_repository_node_id) ||
      !safeRepository(manifest.base_repository) || !safeIdentity(manifest.base_ref) || !commitShaValid(manifest.base_sha) ||
      !commitShaValid(manifest.merge_base_sha) || !sha256Valid(manifest.diff_sha256)) return invalid("changed-path manifest exact identity is invalid");
  if (manifest.changes.length === 0) return invalid("changed-path manifest must not be empty");
  for (const change of manifest.changes) {
    const reason = changeShapeError(change);
    if (reason) return invalid(reason);
  }
  return { ...manifest, sha256: sha256(payload), valid: true, error: "" };
}

function textPath(path) {
  const name = path.split("/").at(-1);
  return ["LICENSE", "NOTICE", "CHANGELOG", "AUTHORS", "CONTRIBUTORS"].includes(name) || [".md", ".txt", ".rst", ".adoc"].some((suffix) => path.endsWith(suffix));
}
function contentKind(path) { return textPath(path) ? "text" : "code"; }
function parentPath(path) { const parts = path.split("/"); return parts.length <= 1 ? "" : parts.slice(0, -1).join("/"); }
function scopeMatches(scope, path) {
  if (["code", "text"].includes(scope.kind)) return scope.kind === contentKind(path);
  if (scope.kind === "file") return scope.path === path;
  if (scope.kind === "directory_files") return scope.path === parentPath(path);
  return scope.kind === "directory_recursive" && path.startsWith(`${scope.path}/`);
}
function anyScopeMatches(scopes, path) { return scopes.some((scope) => scopeMatches(scope, path)); }
function restrictedName(path) {
  const lower = path.toLowerCase();
  return lower === ".env" || lower.endsWith("/.env") || lower.includes("/.env.") || lower.endsWith(".pem") || lower.endsWith(".key") || lower.includes("/secrets/") || lower.includes("/credentials/") || lower.includes("secret_store") || lower.includes("credential_store");
}
function changePaths(change) {
  if (change.status === "renamed") return [change.previous_path, change.path];
  return [change.path];
}
function restrictionReason(manifest) {
  for (const change of manifest.changes) {
    if (change.status !== "deleted" && change.content_kind !== contentKind(change.path)) return "changed-path content classification is not canonical";
    if (change.status !== "added" && change.previous_content_kind !== contentKind(change.previous_path || change.path)) return "changed-path previous content classification is not canonical";
    if (!["ordinary", "absent"].includes(change.semantic_class)) return `immutable semantic restriction matched current content: ${change.semantic_class}`;
    if (!["ordinary", "absent"].includes(change.previous_semantic_class)) return `immutable semantic restriction matched prior content: ${change.previous_semantic_class}`;
    for (const path of changePaths(change)) if (restrictedName(path)) return `immutable self-review restricted path matched: ${path}`;
  }
  return "";
}

function decision(request, policySha, manifestSha, allowed, reason, records = []) {
  return {
    schema: "spipe-self-review-decision/1", allowed, reason,
    matched_constraint_record_ids: records, policy_db_sha256: policySha,
    changed_manifest_sha256: manifestSha, review_evidence_mode: request.review_evidence_mode,
    review_evidence_sha256: request.review_evidence_sha256, repository: request.repository,
    pull_request_number: request.pull_request_number, head_sha: request.head_sha,
    session_id: request.session_id, reviewer_identity: request.reviewer_identity,
    issued_at_unix: request.now_unix, expires_at_unix: request.decision_expires_at_unix,
    target_repository_id: request.target_repository_id, target_ref: request.target_ref,
    target_ruleset_id: request.target_ruleset_id, target_ruleset_version: request.target_ruleset_version,
    target_ruleset_sha256: request.target_ruleset_sha256, base_sha: request.base_sha,
    merge_base_sha: request.merge_base_sha, diff_sha256: request.diff_sha256,
    strict_up_to_date: request.strict_up_to_date, protected_target: request.protected_target,
    provider_action: allowed ? "submit_through_separate_eligible_broker_identity" : "none",
    provider_approval_claimed: false,
  };
}

function recordMatches(record, request, manifest) {
  return record.repository.provider === request.repository_provider && record.repository.id === request.repository_id &&
    record.repository.node_id === request.repository_node_id && record.repository.name === request.repository &&
    record.pull_request_number === request.pull_request_number && record.head_sha === request.head_sha &&
    record.session_id === request.session_id && record.self_reviewer.provider === request.reviewer_provider &&
    record.self_reviewer.identity === request.reviewer_identity && record.self_reviewer.model === request.reviewer_model &&
    record.self_reviewer.tier === request.reviewer_tier && record.self_reviewer.effort === request.reviewer_effort &&
    record.changed_paths_manifest_sha256 === manifest.sha256 && record.review_evidence_sha256 === request.review_evidence_sha256 &&
    request.now_unix >= record.issued_at_unix && request.now_unix < record.expires_at_unix;
}

export function evaluateSelfReview(policy, manifest, request) {
  const reject = (reason, records = []) => decision(request, policy.sha256, manifest.sha256, false, reason, records);
  if (!policy.valid) return reject(policy.error);
  if (!manifest.valid) return reject(manifest.error);
  if (!policy.default_allow || policy.authority !== "operator_owned_external") return reject("self-review policy authority is not default-allow external state");
  if (!request.policy_db_authenticated || !request.changed_manifest_authenticated || !request.provider_resolution_authenticated) return reject("self-review broker authentication evidence is incomplete");
  if (request.expected_policy_db_sha256 !== policy.sha256 || !sha256Valid(policy.sha256)) return reject("self-review request does not bind the authenticated policy database");
  if (!(request.repository_provider === manifest.repository_provider && request.repository_id === manifest.repository_id &&
        request.repository_node_id === manifest.repository_node_id && request.repository === manifest.repository &&
        request.pull_request_number === manifest.pull_request_number && request.head_sha === manifest.head_sha &&
        request.target_repository_id === manifest.base_repository_id && request.target_ref === manifest.base_ref &&
        request.base_sha === manifest.base_sha && request.merge_base_sha === manifest.merge_base_sha && request.diff_sha256 === manifest.diff_sha256))
    return reject("self-review request does not bind the exact provider head/base target identity");
  if (!safeIdentity(request.target_ruleset_id) || !safeIdentity(request.target_ruleset_version) || !sha256Valid(request.target_ruleset_sha256) || !request.strict_up_to_date || !request.protected_target)
    return reject("self-review requires an exact protected target ruleset with strict up-to-date enforcement");
  if (request.author_provider !== request.reviewer_provider || request.author_identity !== request.reviewer_identity) return reject("self-review author and reviewer identities do not match");
  if (![request.session_id, request.reviewer_provider, request.reviewer_identity, request.reviewer_model].every(safeIdentity)) return reject("self-review request identity is invalid");
  if (request.reviewer_tier !== "high_capability" || !["high", "xhigh", "max", "ultra"].includes(request.reviewer_effort)) return reject("self-review requires high-capability review at high effort or above");
  const evidenceModeValid = (request.review_evidence_mode === "broker_signed" && request.review_evidence_broker_authenticated) ||
    (request.review_evidence_mode === "self_attested" && request.self_attestation_authorized && !request.review_evidence_broker_authenticated);
  if (!evidenceModeValid) return reject("review evidence mode is neither broker-signed nor explicitly authorized self-attestation");
  if (request.higher_model_verdict !== "PASS" || request.higher_model_p0_count !== 0 || request.higher_model_p1_count !== 0 || !sha256Valid(request.review_evidence_sha256)) return reject("review evidence is not exact-head PASS with zero P0/P1");
  if (!integer(request.now_unix) || !integer(request.decision_expires_at_unix) || request.now_unix <= 0 || request.decision_expires_at_unix <= request.now_unix || request.decision_expires_at_unix - request.now_unix > policy.max_ttl_seconds) return reject("self-review decision expiry is invalid or exceeds 24 hours");
  const restriction = restrictionReason(manifest);
  if (restriction) return reject(restriction);
  const matched = [];
  for (const record of policy.records) {
    if (!recordMatches(record, request, manifest)) continue;
    if (record.effect === "deny") return reject("operator policy explicitly denies this user/session/head");
    if (manifest.changes.some((change) => changePaths(change).some((path) => anyScopeMatches(record.deny_scopes, path)))) return reject("operator constraint deny scope matched a changed path");
    if (manifest.changes.some((change) => changePaths(change).some((path) => !anyScopeMatches(record.allow_scopes, path)))) return reject("operator constraint does not allow every changed path");
    matched.push(record.record_id);
  }
  return decision(request, policy.sha256, manifest.sha256, true, "default self-review privilege allowed for ordinary code/text; no immutable restriction or operator deny/constrain matched", matched);
}

function remediation(reason, allowed) {
  if (allowed) return "none; if provider state changes or the check expires, review the new exact head and dispatch again";
  if (reason.includes("operator policy explicitly denies")) return "stop; the external policy owner must replace or expire the exact deny, or use an eligible independent-review route";
  if (reason.includes("constraint deny scope") || reason.includes("constraint does not allow")) return "reduce the diff to the allowed scope or obtain a new exact external constraint, then review the new head and dispatch again";
  if (["restricted path", "semantic restriction", "traversal", "symlink", "submodule", "encoding", "unsupported"].some((part) => reason.includes(part))) return "remove the unsafe material or object, rotate any exposed credential, create a clean head, then review and dispatch again";
  if (["policy", "hash chain", "authentication evidence", "evidence mode"].some((part) => reason.includes(part))) return "restore authenticated external policy/evidence with its exact digest and TTL, then rerun from a fresh provider snapshot";
  if (["author and reviewer", "high-capability", "zero P0/P1", "request identity"].some((part) => reason.includes(part))) return "use the exact PR author, high-capability review at high effort or above, and honest exact-head PASS with zero P0/P1; otherwise use an eligible independent reviewer";
  return "resolve the current head/base/diff/ruleset, perform a new high-effort exact-head review with zero P0/P1, then dispatch SPipe Self Review Admission again";
}

function output(decisionValue) {
  const allowed = decisionValue.allowed && decisionValue.issued_at_unix > 0 && decisionValue.issued_at_unix < decisionValue.expires_at_unix;
  return {
    output_version: "simple-release/v1", command: "release self-review-plan",
    status: allowed ? "ok" : "rejected", mutation: "none",
    decision_schema: decisionValue.schema, allowed, reason: decisionValue.reason,
    repository: decisionValue.repository, pull_request_number: decisionValue.pull_request_number,
    head_sha: decisionValue.head_sha, base_sha: decisionValue.base_sha,
    merge_base_sha: decisionValue.merge_base_sha, diff_sha256: decisionValue.diff_sha256,
    target_repository_id: decisionValue.target_repository_id, target_ref: decisionValue.target_ref,
    target_ruleset_id: decisionValue.target_ruleset_id, target_ruleset_version: decisionValue.target_ruleset_version,
    target_ruleset_sha256: decisionValue.target_ruleset_sha256, strict_up_to_date: decisionValue.strict_up_to_date,
    protected_target: decisionValue.protected_target, session_id: decisionValue.session_id,
    reviewer_identity: decisionValue.reviewer_identity, issued_at_unix: decisionValue.issued_at_unix,
    expires_at_unix: decisionValue.expires_at_unix, policy_db_sha256: decisionValue.policy_db_sha256,
    changed_manifest_sha256: decisionValue.changed_manifest_sha256,
    review_evidence_mode: decisionValue.review_evidence_mode,
    review_evidence_sha256: decisionValue.review_evidence_sha256,
    matched_constraint_record_ids: decisionValue.matched_constraint_record_ids,
    provider_action: allowed ? decisionValue.provider_action : "none", provider_approval_claimed: false,
    status_semantics: "required_check_not_github_author_approved_review",
    github_author_approved_review_available: false,
    default_eligibility: "ordinary_code_text_absent_operator_deny_or_constraint",
    remediation: remediation(decisionValue.reason, allowed),
  };
}

export function evaluateFiles(policyPath, manifestPath, requestPath, configuredPolicyPath = process.env.SPIPE_SELF_REVIEW_POLICY_DB) {
  if (!configuredPolicyPath || policyPath !== configuredPolicyPath) throw new Error("self-review policy must come from SPIPE_SELF_REVIEW_POLICY_DB, not the PR worktree");
  const request = parseStrictJson(readFileSync(requestPath, "utf8"));
  if (!closedObject(request, REQUEST_KEYS) || request.schema !== "spipe-self-review-request/1") throw new Error("self-review request must be a closed spipe-self-review-request/1 object");
  for (const key of ["repository_id", "pull_request_number", "now_unix", "decision_expires_at_unix", "higher_model_p0_count", "higher_model_p1_count", "target_repository_id"])
    if (!integer(request[key])) throw new Error(`self-review request ${key} must be an exact integer`);
  for (const key of ["policy_db_authenticated", "changed_manifest_authenticated", "review_evidence_broker_authenticated", "self_attestation_authorized", "strict_up_to_date", "protected_target", "provider_resolution_authenticated"])
    if (typeof request[key] !== "boolean") throw new Error(`self-review request ${key} must be boolean`);
  const policy = parsePolicyDb(readFileSync(policyPath, "utf8"));
  const manifest = parseChangedManifest(readFileSync(manifestPath, "utf8"));
  return output(evaluateSelfReview(policy, manifest, request));
}

function cli(argv) {
  try {
    const expected = ["--policy-db", "--changed-manifest", "--request"];
    if (argv.length !== 3) throw new Error("expected exactly --policy-db, --changed-manifest, and --request");
    const values = new Map();
    for (const argument of argv) {
      const separator = argument.indexOf("=");
      const key = separator < 0 ? argument : argument.slice(0, separator);
      const value = separator < 0 ? "" : argument.slice(separator + 1);
      if (!expected.includes(key) || values.has(key) || value === "") throw new Error("expected exactly one non-empty value for each closed evaluator argument");
      values.set(key, value);
    }
    if (values.size !== expected.length) throw new Error("evaluator arguments are incomplete");
    const result = evaluateFiles(values.get("--policy-db"), values.get("--changed-manifest"), values.get("--request"));
    process.stdout.write(`${JSON.stringify(result)}\n`);
    return result.allowed ? 0 : 1;
  } catch (error) {
    process.stdout.write(`${JSON.stringify({ output_version: "simple-release/v1", command: "release self-review-plan", status: "rejected", mutation: "none", reason: error.message, provider_approval_claimed: false, status_semantics: "required_check_not_github_author_approved_review", github_author_approved_review_available: false, remediation: remediation(error.message, false) })}\n`);
    return 1;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) process.exitCode = cli(process.argv.slice(2));
