import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { initializeResult } from "../../mcp/protocol/initialize.js";
import { tools, callTool } from "../../mcp/protocol/tools.js";
import {
  canonicalProjectionSemanticHash,
  projectionSemanticHash,
  releaseContractHash
} from "../../src/release/contract.js";
import { createReleasePlan } from "../../src/release/planner.js";

const root = new URL("../../", import.meta.url).pathname;

test("plugin release schemas and identities stay at 0.2.0", () => {
  assert.equal(initializeResult().serverInfo.version, "0.2.0");
  assert.equal(JSON.parse(readFileSync(join(root, "package.json"), "utf8")).version, "0.2.0");
  const manifest = readFileSync(join(root, "plugin/manifest.sdn"), "utf8");
  assert.match(manifest, /version: 0\.2\.0/);
  assert.match(manifest, /reviewed_beta_backports: true/);
  assert.match(manifest, /immutable_release_candidates: true/);
  assert.match(manifest, /promote_without_rebuild: true/);
  assert.match(manifest, /operational_release_planning: true/);
  assert.match(manifest, /main_fix_discovery_planning: true/);
  assert.match(manifest, /release_first_forward_port_validation: true/);
  assert.match(manifest, /external_release_mutation: false/);
});

test("MCP exposes read-only release policy surfaces", () => {
  assert.ok(tools.some((tool) => tool.name === "spipe_release_guide"));
  assert.ok(tools.some((tool) => tool.name === "spipe_release_capabilities"));
  for (const name of [
    "spipe_release_session_plan",
    "spipe_release_beta_backport_plan",
    "spipe_release_candidate_plan",
    "spipe_release_promotion_plan",
    "spipe_release_main_fix_discovery_plan",
    "spipe_release_forward_port_plan"
  ]) assert.ok(tools.some((tool) => tool.name === name), `missing MCP planner: ${name}`);
  const capabilities = callTool(root, "spipe_release_capabilities").content[0].text;
  assert.match(capabilities, /immutable_release_candidates=true/);
  assert.match(capabilities, /promote_without_rebuild=true/);
  assert.match(capabilities, /external_release_mutation=false/);
  assert.match(capabilities, new RegExp(`contract_sha256=${releaseContractHash()}`));
});

test("CLI, MCP, manifest, and plugin descriptor expose the same release policy", () => {
  const manifest = readFileSync(join(root, "plugin/manifest.sdn"), "utf8");
  const descriptor = JSON.parse(readFileSync(join(root, "plugin/.codex-plugin/plugin.json"), "utf8"));
  const contractSource = readFileSync(join(root, "src/release/contract.js"), "utf8");
  const mcpCapabilities = callTool(root, "spipe_release_capabilities").content[0].text;
  for (const capability of [
    "isolated_sessions",
    "reviewed_beta_backports",
    "immutable_release_candidates",
    "promote_without_rebuild",
    "operational_release_planning",
    "main_fix_discovery_planning",
    "release_first_forward_port_validation"
  ]) {
    assert.match(manifest, new RegExp(`${capability}: true`));
    assert.match(contractSource, new RegExp(`${capability}: true`));
    assert.match(mcpCapabilities, new RegExp(`${capability}=true`));
  }
  assert.equal(descriptor.skills, "./skills/");
  assert.deepEqual(descriptor.interface.capabilities, ["Read", "Planning"]);
  assert.equal(Object.hasOwn(descriptor, "commands"), false);
  for (const path of [
    "plugin/skills/software-release/SKILL.md",
    "plugin/skills/release/SKILL.md",
    "plugin/skills/sync/SKILL.md"
  ]) assert.ok(readFileSync(join(root, path), "utf8").length > 0, `missing installed skill: ${path}`);
});

test("guarded planners bind exact evidence and never perform mutation", () => {
  const sha = "a".repeat(40);
  const hash = "b".repeat(64);
  const session = createReleasePlan("isolated-session", {
    session_id: "s-release-001", branch: "work/release/v1.2.0-beta.1-s-release-001",
    workspace: "/tmp/release-s-release-001", main_workspace: "/repo", target_ref: "release/1.2",
    base_commit_sha: sha, policy_sha256: hash, unique_branch: true, unique_workspace: true, main_worktree: false
  });
  assert.equal(session.mutation, "none");
  assert.equal(session.contract_sha256, releaseContractHash());
  const backport = createReleasePlan("beta-backport", {
    version: "1.2.0-beta.1", source_commit_sha: sha, review_receipt_sha256: hash,
    source_result_sha256: hash, target_result_sha256: "c".repeat(64), reviewed: true,
    caller_selected: true, focused_tests_renewed: true, automatic_selection: false
  });
  assert.equal(backport.operation, "beta-backport");
  const candidate = createReleasePlan("candidate", {
    version: "1.2.0-beta.1", attempt: 1, candidate_ref: "candidate/v1.2.0-beta.1/a001",
    commit_sha: sha, source_tree_sha256: hash, policy_sha256: hash,
    artifact_manifest_sha256: hash, qualification_sha256: hash,
    create_once: true, build_once: true, fallback_used: false
  });
  assert.equal(candidate.operation, "candidate");
  const promotion = JSON.parse(callTool(root, "spipe_release_promotion_plan", {
    version: "1.2.0-beta.1", tag: "v1.2.0-beta.1", candidate_commit_sha: sha,
    candidate_identity_sha256: hash, admission_sha256: hash,
    artifact_manifest_sha256: hash, policy_sha256: hash, admitted: true,
    signed_annotated_tag: true, release_authority_approved: true,
    rebuild: false, move_or_delete_existing_tag: false
  }).content[0].text);
  assert.equal(promotion.mutation, "none");
  assert.match(promotion.next_action, /no push, tag, delete, rebuild, or publication/);
});

test("beta convergence discovers main fixes but requires selection and validates forward-port", () => {
  const sha = "a".repeat(40);
  const hash = "b".repeat(64);
  const discovery = createReleasePlan("main-fix-discovery", {
    main_commit_sha: sha, since_commit_sha: "c".repeat(40), read_only_snapshot: true,
    candidates: [
      { commit_sha: "d".repeat(40), title: "fix parser", classification: "bug-fix", reviewed: true, changed_paths: ["src/parser.spl"] },
      { commit_sha: "e".repeat(40), title: "new syntax", classification: "feature", reviewed: true, changed_paths: ["src/parser.spl"] }
    ]
  });
  assert.equal(discovery.inputs.eligible_candidates.length, 1);
  assert.equal(discovery.inputs.caller_selection_required, true);
  assert.equal(discovery.inputs.automatic_selection, false);
  const forwardPort = createReleasePlan("forward-port", {
    release_fix_commit_sha: sha, main_base_commit_sha: "c".repeat(40),
    review_receipt_sha256: hash, main_result_sha256: hash,
    release_first_exception_approved: true, reviewed: true, main_tests_renewed: true,
    protected_ref_direct_update: false, forward_port_branch: "work/fix/gh-1-forward-port-parser"
  });
  assert.equal(forwardPort.mutation, "none");
  assert.match(forwardPort.next_action, /do not push main directly/);
});

test("guarded planners fail closed on unsafe requests", () => {
  const hash = "b".repeat(64);
  assert.throws(() => createReleasePlan("isolated-session", {
    session_id: "s", branch: "main", workspace: "/repo", main_workspace: "/repo", target_ref: "main",
    base_commit_sha: "a".repeat(40), policy_sha256: hash,
    unique_branch: false, unique_workspace: false, main_worktree: true
  }), /unique_branch must be true/);
  assert.throws(() => createReleasePlan("beta-backport", {
    version: "1.2.0-beta.1", source_commit_sha: "a".repeat(40), review_receipt_sha256: hash,
    source_result_sha256: hash, target_result_sha256: hash, reviewed: true,
    caller_selected: true, focused_tests_renewed: true, automatic_selection: true
  }), /automatic_selection must be false/);
  assert.throws(() => createReleasePlan("candidate", {
    version: "1.2.0-beta.1", attempt: 2, candidate_ref: "candidate/v1.2.0-beta.1/a001",
    commit_sha: "a".repeat(40), source_tree_sha256: hash, policy_sha256: hash,
    artifact_manifest_sha256: hash, qualification_sha256: hash,
    create_once: true, build_once: true, fallback_used: false
  }), /a002/);
  assert.throws(() => createReleasePlan("promotion", {
    version: "1.2.0-beta.1", tag: "v1.2.0-beta.1", candidate_commit_sha: "a".repeat(40),
    candidate_identity_sha256: hash, admission_sha256: hash,
    artifact_manifest_sha256: hash, policy_sha256: hash, admitted: true,
    signed_annotated_tag: true, release_authority_approved: true,
    rebuild: true, move_or_delete_existing_tag: false
  }), /rebuild must be false/);
});

test("release projections have one hashed semantic contract", () => {
  const paths = [
    "doc/00_llm_process/skill_command/command/release.md",
    "doc/00_llm_process/skill_command/skills/codex/release/skill.md",
    "doc/00_llm_process/skill_command/skills/gemini/release/skill.md",
    "doc/00_llm_process/skill_command/skills/pipe/release/skill.md",
    ".claude/skills/software-release.md",
    ".codex/skills/software-release/SKILL.md"
  ];
  const expected = canonicalProjectionSemanticHash();
  for (const path of paths) {
    const content = readFileSync(join(root, path), "utf8");
    assert.equal(projectionSemanticHash(content), expected, `${path}: semantic release projection drift`);
  }
});

test("canonical release guidance rejects legacy unsafe behavior", () => {
  const paths = [
    "doc/00_llm_process/skill_command/command/release.md",
    "doc/00_llm_process/skill_command/skills/codex/release/skill.md",
    "doc/00_llm_process/skill_command/skills/gemini/release/skill.md",
    "doc/00_llm_process/skill_command/skills/pipe/release/skill.md",
    "doc/00_llm_process/skill_command/skills/pipe/release/repo_and_pull_req/skill.md"
  ];
  const guide = readFileSync(join(root, paths[0]), "utf8");
  for (const path of paths) {
    const content = readFileSync(join(root, path), "utf8");
    for (const forbidden of ["git push --tags", "bookmark set main", "gh release delete", "git tag -d", "NO BRANCHES"])
      assert.equal(content.includes(forbidden), false, `${path}: forbidden legacy command: ${forbidden}`);
  }
  assert.match(guide, /reviewed bug-fix commit/);
  assert.match(guide, /Promotion never rebuilds/);
});
