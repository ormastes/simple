import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";

import {
  evaluateFiles,
  evaluateSelfReview,
  parseChangedManifest,
  parsePolicyDb,
} from "../../../../scripts/release/self-review-policy-evaluator.mjs";

const HASH_A = "a".repeat(64);
const HASH_B = "b".repeat(64);
const HEAD = "1".repeat(40);
const BASE = "2".repeat(40);
const MERGE = "3".repeat(40);
const NOW = 1787847000;
const EXPIRES = 1787847300;
const sha256 = (value) => createHash("sha256").update(value, "utf8").digest("hex");

function manifest(path = "README.md", kind = "text", previousPath = "") {
  const status = previousPath ? "renamed" : "modified";
  const previousKind = previousPath?.endsWith(".md") ? "text" : previousPath ? "code" : kind;
  return [
    "schema: spipe-changed-path-manifest/1",
    "repository_provider: github",
    "repository_id: 1175797696",
    "repository_node_id: R_kgDORhU_wA",
    "repository: ormastes/simple",
    "pull_request_number: 83",
    `head_sha: ${HEAD}`,
    "base_repository_provider: github",
    "base_repository_id: 1175797696",
    "base_repository_node_id: R_kgDORhU_wA",
    "base_repository: ormastes/simple",
    "base_ref: refs/heads/main",
    `base_sha: ${BASE}`,
    `merge_base_sha: ${MERGE}`,
    `diff_sha256: ${HASH_B}`,
    "changes:",
    `  - status: ${status}`,
    `    path: ${path}`,
    previousPath ? `    previous_path: ${previousPath}` : "    previous_path:",
    `    content_kind: ${kind}`,
    `    previous_content_kind: ${previousKind}`,
    "    semantic_class: ordinary",
    "    previous_semantic_class: ordinary",
    "    file_type: regular",
    "    previous_file_type: regular",
    "    encoding: utf8",
    "    previous_encoding: utf8",
    "",
  ].join("\n");
}

function policy(manifestSha, effect = "", allowScopes = [], denyScopes = []) {
  const header = { schema: "spipe-self-review-policy-db/1", default_allow: true, max_ttl_seconds: 86400, authority: "operator_owned_external" };
  if (!effect) return JSON.stringify(header);
  const record = {
    schema: "spipe-self-review-policy-db/grant/1", record_id: "record-1", effect,
    repository: { provider: "github", id: 1175797696, node_id: "R_kgDORhU_wA", name: "ormastes/simple" },
    pull_request_number: 83, head_sha: HEAD, session_id: "session/83",
    self_reviewer: { provider: "github", identity: "2378857", model: "codex/gpt-5.6-sol", tier: "high_capability", effort: "xhigh" },
    changed_paths_manifest_sha256: manifestSha, review_evidence_sha256: HASH_A,
    allow_scopes: allowScopes, deny_scopes: denyScopes,
    issuer: { provider: "github", identity: "ormastes", key_id: "operator-key-1" },
    issued_at_unix: 1787846400, expires_at_unix: EXPIRES,
    previous_record_sha256: "0".repeat(64), signature: "s".repeat(32),
  };
  return `${JSON.stringify(header)}\n${JSON.stringify(record)}`;
}

function request(policySha) {
  return {
    schema: "spipe-self-review-request/1", repository_provider: "github",
    repository_id: 1175797696, repository_node_id: "R_kgDORhU_wA", repository: "ormastes/simple",
    pull_request_number: 83, head_sha: HEAD, session_id: "session/83",
    author_provider: "github", author_identity: "2378857", reviewer_provider: "github",
    reviewer_identity: "2378857", reviewer_model: "codex/gpt-5.6-sol",
    reviewer_tier: "high_capability", reviewer_effort: "xhigh", review_evidence_mode: "self_attested",
    now_unix: NOW, decision_expires_at_unix: EXPIRES, higher_model_verdict: "PASS",
    higher_model_p0_count: 0, higher_model_p1_count: 0, review_evidence_sha256: HASH_A,
    expected_policy_db_sha256: policySha, policy_db_authenticated: true,
    changed_manifest_authenticated: true, review_evidence_broker_authenticated: false,
    self_attestation_authorized: true, target_repository_id: 1175797696,
    target_ref: "refs/heads/main", target_ruleset_id: "github:ruleset:123",
    target_ruleset_version: "spipe-vcs-v3-main", target_ruleset_sha256: HASH_B,
    base_sha: BASE, merge_base_sha: MERGE, diff_sha256: HASH_B,
    strict_up_to_date: true, protected_target: true, provider_resolution_authenticated: true,
  };
}

function evaluate(policyPayload, manifestPayload) {
  const parsedPolicy = parsePolicyDb(policyPayload);
  const parsedManifest = parseChangedManifest(manifestPayload);
  return evaluateSelfReview(parsedPolicy, parsedManifest, request(parsedPolicy.sha256));
}

test("tracked adapter preserves Simple v1 default-allow output without claiming GitHub approval", () => {
  const changed = manifest();
  const decision = evaluate(policy(sha256(changed)), changed);
  assert.equal(decision.allowed, true);
  assert.equal(decision.schema, "spipe-self-review-decision/1");
  assert.equal(decision.provider_action, "submit_through_separate_eligible_broker_identity");
  assert.equal(decision.provider_approval_claimed, false);
  assert.deepEqual(decision.matched_constraint_record_ids, []);
});

test("tracked adapter preserves Simple v1 deny and constrain precedence", () => {
  const changed = manifest("doc/guide.md");
  const changedSha = sha256(changed);
  assert.match(evaluate(policy(changedSha, "deny"), changed).reason, /explicitly denies/);

  const allowDoc = [{ kind: "directory_recursive", path: "doc" }];
  const constrained = evaluate(policy(changedSha, "constrain", allowDoc), changed);
  assert.equal(constrained.allowed, true);
  assert.deepEqual(constrained.matched_constraint_record_ids, ["record-1"]);

  const denied = evaluate(policy(changedSha, "constrain", allowDoc, [{ kind: "file", path: "doc/guide.md" }]), changed);
  assert.equal(denied.allowed, false);
  assert.match(denied.reason, /deny scope/);
});

test("tracked adapter checks both names of a rename against each constraint", () => {
  const changed = manifest("doc/new.md", "text", "src/old.spl");
  const allowDoc = [{ kind: "directory_recursive", path: "doc" }];
  const decision = evaluate(policy(sha256(changed), "constrain", allowDoc), changed);
  assert.equal(decision.allowed, false);
  assert.match(decision.reason, /does not allow every changed path/);
});

test("tracked adapter fails closed on duplicate policy keys and non-ASCII path aliases", () => {
  const duplicateHeader = '{"schema":"spipe-self-review-policy-db/1","schema":"spipe-self-review-policy-db/1","default_allow":true,"max_ttl_seconds":86400,"authority":"operator_owned_external"}';
  assert.equal(parsePolicyDb(duplicateHeader).valid, false);
  assert.equal(parseChangedManifest(manifest("doc/café.md")).valid, false);
});

test("file adapter requires the secret path and a closed exact request", () => {
  const directory = mkdtempSync(join(tmpdir(), "self-review-evaluator-"));
  try {
    const changed = manifest();
    const policyPayload = policy(sha256(changed));
    const policyPath = join(directory, "policy.jsonl");
    const manifestPath = join(directory, "manifest.sdn");
    const requestPath = join(directory, "request.json");
    writeFileSync(policyPath, policyPayload);
    writeFileSync(manifestPath, changed);
    writeFileSync(requestPath, JSON.stringify(request(sha256(policyPayload))));
    const result = evaluateFiles(policyPath, manifestPath, requestPath, policyPath);
    assert.equal(result.status, "ok");
    assert.equal(result.decision_schema, "spipe-self-review-decision/1");
    assert.equal(result.provider_approval_claimed, false);

    writeFileSync(requestPath, JSON.stringify({ ...request(sha256(policyPayload)), unexpected: true }));
    assert.throws(() => evaluateFiles(policyPath, manifestPath, requestPath, policyPath), /closed/);
    assert.throws(() => evaluateFiles(policyPath, manifestPath, requestPath, join(directory, "other")), /SPIPE_SELF_REVIEW_POLICY_DB/);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
