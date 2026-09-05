# Unified local lifecycle admission

> This scenario shows maintainers how a logical change becomes exact review and gate evidence, then a protected dry-run plan and a conflict-safe remote projection. It deliberately performs no Git/JJ/provider mutation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified local lifecycle admission

This scenario shows maintainers how a logical change becomes exact review and gate evidence, then a protected dry-run plan and a conflict-safe remote projection. It deliberately performs no Git/JJ/provider mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/scv_jj_git_devhub_spipe_unified_lifecycle.md |
| Plan | doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md |
| Design | doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md |
| Research | doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_2026-08-25.md |
| Source | `test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario shows maintainers how a logical change becomes exact review and
gate evidence, then a protected dry-run plan and a conflict-safe remote
projection. It deliberately performs no Git/JJ/provider mutation.

## Requirements

**Requirements:** doc/02_requirements/feature/scv_jj_git_devhub_spipe_unified_lifecycle.md

**Research:** doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_2026-08-25.md

**Plan:** doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md

**Design:** doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md

## Operator flow

Run this scenario before promoting the typed lifecycle base. The primary path
must bind one exact immutable revision to its approval and non-vacuous gate
bundle, produce a dry-run plan containing compare-and-swap, and retain a
concurrent provider edit as a conflict.

## Example

Run the focused system scenario with the admitted self-hosted Simple CLI. A
successful run reports two examples, zero failures, an exact-revision admitted
dry-run, and a stale-CAS refusal.

## Troubleshooting

- `SJ_REMOTE_STALE` means the observed remote revision changed; fetch, refresh,
  and re-review rather than forcing the ref.
- `LIFECYCLE_GATE_INCOMPLETE` means a gate has no retained evidence, a verdict
  is not pass, or an approval is missing/stale.
- A sync `conflict` is durable work to resolve, never permission to overwrite.

## Scenarios

### Unified SCV, SJ, DevHub, and Spipe lifecycle

#### plans an exact reviewed integration without mutating protected state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans an exact reviewed integration without mutating protected state
- Load the unified lifecycle policy
- Create stable change and immutable revision identities
- Bind review and gate evidence to the exact revision
- Plan a protected integration without mutating refs
   - Expected: plan.message equals `dry-run only; no refs mutated`
   - Expected: plan.gate_invocation_ids equals `["conflict-tree", "rules"]`
- Project lifecycle state without silent conflict loss
   - Expected: sync.action equals `conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plans an exact reviewed integration without mutating protected state")
step("Load the unified lifecycle policy")
val policy_payload = unified_policy_fixture()
val policy = parse_lifecycle_vcs_policy(policy_payload)
expect(policy.valid).to_be(true)
expect(lifecycle_policy_ref(policy, "integration/main") != nil).to_be(true)

step("Create stable change and immutable revision identities")
val change = lifecycle_change_identity("agent-base", "Unified lifecycle", "dev-infra", "typed observe-only base")
val revision = lifecycle_revision_identity(change.change_id, "tree-1", ["rev-base"], "policy-significant metadata", lifecycle_aliases("jj-change", "jj-commit", "git-commit", []))
expect(change.change_id).to_start_with("chg_")
expect(revision.revision_id).to_start_with("rev_")

step("Bind review and gate evidence to the exact revision")
val review = lifecycle_open_review("REV-101", change.change_id, "rev-base", revision.revision_id, "integration/main", "standard")
val approval = lifecycle_approval(review, ApprovalEvidence(revision_id: revision.revision_id, tree_digest: "tree-1", reviewer: "independent-reviewer", authority: "maintainer", policy_digest: policy.digest, evidence_digest: "evidence-1", created_at: "2026-08-25T00:00:00Z"))
val conflict_run = GateRun(gate_run_id: "GATE-1", revision_id: revision.revision_id, gate_id: "conflict-tree", policy_digest: policy.digest, tool_digest: "tool-1", environment_digest: "env-1", verdict: "pass", evidence_objects: ["log-1"])
val rules_run = GateRun(gate_run_id: "GATE-2", revision_id: revision.revision_id, gate_id: "rules", policy_digest: policy.digest, tool_digest: "tool-1", environment_digest: "env-1", verdict: "pass", evidence_objects: ["log-2"])
val bundle = lifecycle_gate_bundle("BUNDLE-1", revision.revision_id, [conflict_run, rules_run], [approval], policy.digest)
expect(bundle.complete).to_be(true)

step("Plan a protected integration without mutating refs")
val request = IntegrateRequest(change_id: change.change_id, revision_id: revision.revision_id, base_revision_id: "rev-base", expected_remote_revision: "git-main-1", observed_remote_revision: "git-main-1", target_ref: "integration/main", policy_digest: policy.digest, gate_profile: "standard", actor: "agent", authority: "maintainer", dry_run: true)
val gate_plan = plan_protected_gate_manifest(parse_gate_manifest(unified_gate_fixture()), "rev-base", revision.revision_id)
val plan = plan_integration_with_policy(request, [approval], [conflict_run, rules_run], bundle, policy_payload, gate_plan)
expect(plan.admitted).to_be(true)
expect(plan.message).to_equal("dry-run only; no refs mutated")
expect(plan.steps).to_contain("compare_and_swap_integration_ref")
expect(plan.gate_invocation_ids).to_equal(["conflict-tree", "rules"])

step("Project lifecycle state without silent conflict loss")
val binding = RemoteBinding(binding_id: "BIND-1", entity_type: "feature", entity_id: "FEAT-1", provider_instance: "github", remote_kind: "issue", remote_id: "42", remote_revision: "etag-2", authority_policy_id: "field-split", sync_base_digest: "base", state: "bound")
val sync = lifecycle_sync_field(binding, "status", "open", "implementing", "blocked", "field_split")
expect(sync.action).to_equal("conflict")
```

</details>

#### refuses stale remote compare-and-swap state

- refuses stale remote compare-and-swap state
   - Expected: plan_integration(request, [approval], bundle, true).code equals `SJ_REMOTE_STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses stale remote compare-and-swap state")
val change = lifecycle_change_identity("stale-agent", "Stale integration", "dev-infra", "reject stale CAS")
val revision = lifecycle_revision_identity(change.change_id, "tree-2", ["rev-base"], "metadata", lifecycle_aliases("", "", "", []))
val review = lifecycle_open_review("REV-STALE", change.change_id, "rev-base", revision.revision_id, "integration/main", "standard")
val approval = lifecycle_approval(review, ApprovalEvidence(revision_id: revision.revision_id, tree_digest: "tree-2", reviewer: "reviewer", authority: "maintainer", policy_digest: "policy-1", evidence_digest: "evidence-1", created_at: "2026-08-25T00:00:00Z"))
val run = GateRun(gate_run_id: "GATE-STALE", revision_id: revision.revision_id, gate_id: "changed-scope", policy_digest: "policy-1", tool_digest: "tool-1", environment_digest: "env-1", verdict: "pass", evidence_objects: ["log-1"])
val bundle = lifecycle_gate_bundle("BUNDLE-STALE", revision.revision_id, [run], [approval], "policy-1")
val request = IntegrateRequest(change_id: change.change_id, revision_id: revision.revision_id, base_revision_id: "rev-base", expected_remote_revision: "git-main-1", observed_remote_revision: "git-main-2", target_ref: "integration/main", policy_digest: "policy-1", gate_profile: "standard", actor: "agent", authority: "maintainer", dry_run: true)
expect(plan_integration(request, [approval], bundle, true).code).to_equal("SJ_REMOTE_STALE")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/scv_jj_git_devhub_spipe_unified_lifecycle.md`
- **Plan:** `doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md`
- **Design:** `doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md`
- **Research:** `doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_2026-08-25.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ef678379409c68ca681b7ca6de5e6995172786858445bb912c07483686bd92c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ef678379409c68ca681b7ca6de5e6995172786858445bb912c07483686bd92c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ef678379409c68ca681b7ca6de5e6995172786858445bb912c07483686bd92c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=91; blocker cap makes effective=49
doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
