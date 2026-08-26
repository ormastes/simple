import { digest, releaseContractHash } from "./contract.js";

const SHA1 = /^[0-9a-f]{40}$/;
const SHA256 = /^[0-9a-f]{64}$/;
const VERSION = /^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(?:-(?:alpha|beta|rc)\.(0|[1-9][0-9]*))?$/;

function requireText(input, key) {
  if (typeof input[key] !== "string" || input[key].trim() === "") throw new Error(`${key} is required`);
  return input[key];
}

function requireMatch(input, key, pattern) {
  const value = requireText(input, key);
  if (!pattern.test(value)) throw new Error(`${key} has invalid format`);
  return value;
}

function requireTrue(input, key) {
  if (input[key] !== true) throw new Error(`${key} must be true`);
}

function requireFalse(input, key) {
  if (input[key] !== false) throw new Error(`${key} must be false`);
}

function plan(operation, inputs, checks, nextAction) {
  const body = {
    schema: "spipe-release-plan/1",
    operation,
    contract_sha256: releaseContractHash(),
    mutation: "none",
    external_authority_required: true,
    checks,
    next_action: nextAction,
    inputs
  };
  return Object.freeze({ ...body, plan_sha256: digest(body) });
}

export function planIsolatedSession(input) {
  const sessionId = requireText(input, "session_id");
  const branch = requireText(input, "branch");
  const workspace = requireText(input, "workspace");
  const target = requireText(input, "target_ref");
  requireMatch(input, "base_commit_sha", SHA1);
  requireMatch(input, "policy_sha256", SHA256);
  requireTrue(input, "unique_branch");
  requireTrue(input, "unique_workspace");
  requireFalse(input, "main_worktree");
  if (!branch.startsWith("work/")) throw new Error("branch must be an owned work/* ref");
  if (workspace === input.main_workspace) throw new Error("workspace must not be the main worktree");
  if (target !== "main" && !/^release\/[0-9]+\.[0-9]+$/.test(target)) throw new Error("target_ref must be main or release/X.Y");
  return plan("isolated-session", { ...input, session_id: sessionId }, [
    "unique owned work branch", "unique non-main workspace", "exact base commit", "policy digest bound"
  ], "create the session only through an authorized workspace/session provider");
}

export function planBetaBackport(input) {
  const version = requireMatch(input, "version", VERSION);
  if (!version.includes("-beta.")) throw new Error("version must be a numbered beta prerelease");
  requireMatch(input, "source_commit_sha", SHA1);
  requireMatch(input, "review_receipt_sha256", SHA256);
  requireMatch(input, "source_result_sha256", SHA256);
  requireMatch(input, "target_result_sha256", SHA256);
  requireTrue(input, "reviewed");
  requireTrue(input, "caller_selected");
  requireTrue(input, "focused_tests_renewed");
  requireFalse(input, "automatic_selection");
  return plan("beta-backport", input, [
    "exact source commit", "review receipt bound", "caller-selected bug fix", "target evidence renewed"
  ], "apply this exact commit in the isolated beta work branch, then renew admission evidence");
}

export function planMainFixDiscovery(input) {
  requireMatch(input, "main_commit_sha", SHA1);
  requireMatch(input, "since_commit_sha", SHA1);
  requireTrue(input, "read_only_snapshot");
  if (!Array.isArray(input.candidates)) throw new Error("candidates must be an array");
  const eligible = input.candidates.map((candidate, index) => {
    if (!candidate || typeof candidate !== "object") throw new Error(`candidates[${index}] must be an object`);
    requireMatch(candidate, "commit_sha", SHA1);
    requireText(candidate, "title");
    requireText(candidate, "classification");
    if (!Array.isArray(candidate.changed_paths)) throw new Error(`candidates[${index}].changed_paths must be an array`);
    return candidate;
  }).filter((candidate) => candidate.classification === "bug-fix" && candidate.reviewed === true);
  return plan("main-fix-discovery", {
    ...input,
    eligible_candidates: eligible.map((candidate) => ({
      commit_sha: candidate.commit_sha,
      title: candidate.title,
      changed_paths: candidate.changed_paths
    })),
    caller_selection_required: true,
    automatic_selection: false
  }, ["immutable main snapshot", "exact commit identities", "reviewed bug-fix classification only"],
  "present eligible fixes to the caller; do not cherry-pick until the caller selects one exact commit");
}

export function planForwardPort(input) {
  requireMatch(input, "release_fix_commit_sha", SHA1);
  requireMatch(input, "main_base_commit_sha", SHA1);
  requireMatch(input, "review_receipt_sha256", SHA256);
  requireMatch(input, "main_result_sha256", SHA256);
  requireTrue(input, "release_first_exception_approved");
  requireTrue(input, "reviewed");
  requireTrue(input, "main_tests_renewed");
  requireFalse(input, "protected_ref_direct_update");
  const branch = requireText(input, "forward_port_branch");
  if (!branch.startsWith("work/backport/") && !branch.startsWith("work/fix/"))
    throw new Error("forward_port_branch must be an isolated work/backport/* or work/fix/* ref");
  return plan("forward-port", input, [
    "exact release-first fix", "exception approval bound", "isolated main-target branch", "main evidence renewed"
  ], "submit the isolated forward-port branch through protected main integration; do not push main directly");
}

export function planCandidate(input) {
  const version = requireMatch(input, "version", VERSION);
  const attempt = Number(input.attempt);
  if (!Number.isSafeInteger(attempt) || attempt < 1 || attempt > 999) throw new Error("attempt must be an integer from 1 through 999");
  const expectedRef = `candidate/v${version}/a${String(attempt).padStart(3, "0")}`;
  if (input.candidate_ref !== expectedRef) throw new Error(`candidate_ref must equal ${expectedRef}`);
  requireMatch(input, "commit_sha", SHA1);
  for (const key of ["source_tree_sha256", "policy_sha256", "artifact_manifest_sha256", "qualification_sha256"])
    requireMatch(input, key, SHA256);
  requireTrue(input, "create_once");
  requireTrue(input, "build_once");
  requireFalse(input, "fallback_used");
  return plan("candidate", input, [
    "candidate ref is canonical", "source and policy fixed", "artifact and qualification receipts bound", "no fallback"
  ], "request create-once candidate admission from the protected candidate authority");
}

export function planPromotion(input) {
  const version = requireMatch(input, "version", VERSION);
  if (input.tag !== `v${version}`) throw new Error(`tag must equal v${version}`);
  requireMatch(input, "candidate_commit_sha", SHA1);
  for (const key of ["candidate_identity_sha256", "admission_sha256", "artifact_manifest_sha256", "policy_sha256"])
    requireMatch(input, key, SHA256);
  requireTrue(input, "admitted");
  requireTrue(input, "signed_annotated_tag");
  requireTrue(input, "release_authority_approved");
  requireFalse(input, "rebuild");
  requireFalse(input, "move_or_delete_existing_tag");
  return plan("promotion", input, [
    "exact admitted candidate", "exact artifact manifest", "signed annotated immutable tag", "promotion does not rebuild"
  ], "submit this plan to the protected release authority; this tool performs no push, tag, delete, rebuild, or publication");
}

export function createReleasePlan(operation, input) {
  if (!input || typeof input !== "object" || Array.isArray(input)) throw new Error("input must be a JSON object");
  if (operation === "isolated-session") return planIsolatedSession(input);
  if (operation === "beta-backport") return planBetaBackport(input);
  if (operation === "candidate") return planCandidate(input);
  if (operation === "promotion") return planPromotion(input);
  if (operation === "main-fix-discovery") return planMainFixDiscovery(input);
  if (operation === "forward-port") return planForwardPort(input);
  throw new Error(`unknown release planning operation: ${operation}`);
}
