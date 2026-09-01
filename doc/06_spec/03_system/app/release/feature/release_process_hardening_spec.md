# Protected beta and stable software release

> This manual shows a release operator how Simple and Spipe validate a beta or stable release before any VCS, build, signing, or hosting provider mutates external state. The executable scenarios exercise pure plans only. A local PASS does not claim that GitHub rulesets, signing keys, protected pushes, immutable publication, or registries were changed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protected beta and stable software release

This manual shows a release operator how Simple and Spipe validate a beta or stable release before any VCS, build, signing, or hosting provider mutates external state. The executable scenarios exercise pure plans only. A local PASS does not claim that GitHub rulesets, signing keys, protected pushes, immutable publication, or registries were changed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/release_process_hardening.md |
| Plan | doc/03_plan/sys_test/release_process_hardening.md |
| Design | doc/05_design/release_process_hardening.md |
| Research | doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md |
| Source | `test/03_system/app/release/feature/release_process_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This manual shows a release operator how Simple and Spipe validate a beta or
stable release before any VCS, build, signing, or hosting provider mutates
external state. The executable scenarios exercise pure plans only. A local PASS
does not claim that GitHub rulesets, signing keys, protected pushes, immutable
publication, or registries were changed.

## Requirements

**Requirements:** doc/02_requirements/feature/release_process_hardening.md

**NFRs:** doc/02_requirements/nfr/release_process_hardening.md

**Research:** doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md

**Plan:** doc/03_plan/sys_test/release_process_hardening.md

**Architecture:** doc/04_architecture/release_process_hardening.md

**Design:** doc/05_design/release_process_hardening.md

## Operator flow

Begin in an isolated release session with a unique work branch and worktree.
Load the canonical version and protected-ref policy. For beta maintenance,
target the matching release line and validate one explicit reviewed bug fix at
a time. After renewed focused evidence passes for the resulting revision,
integrate through compare-and-swap and freeze a new immutable candidate.

Build and qualify that exact candidate once. Promotion consumes the admitted
artifact manifest without rebuilding or fallback and prepares one signed,
annotated, exact tag ref. Rollback redeploys an older admitted version;
withdrawal never deletes, moves, or reuses release identity.

## Commands

Use the shipped validation commands before provider mutation:

```text
simple release version-check
simple release beta-prepare
simple release backport-check
simple release candidate-check
simple release promote-check
simple release withdraw-check
```

The Spipe plugin exposes `spipe release-guide` and
`spipe release-capabilities` as read-only discovery surfaces.

## Examples

A valid beta identity is `1.4.0-beta.2` on `release/1.4`; its first immutable
candidate is `candidate/v1.4.0-beta.2/a001` and its eventual signed tag is
`v1.4.0-beta.2`. Uppercase or unnumbered beta suffixes are invalid for new
releases. A backport with `kind=feat` is rejected even when its commit and
review fields are present. A promotion plan with matching artifacts is still
rejected when it requests a rebuild, fallback, unsigned tag, or broad tag push.

## Beta backport evidence

A valid beta backport records the exact source SHA, stable change and work IDs,
change kind `fix`, review receipt digest, target `release/X.Y`, expected target
SHA, explicit adaptation reason, result SHA, and renewed evidence digest. Reject
feature commits, commit ranges, moving refs, stale review, wrong release line,
or evidence from before the backport was applied.

## Candidate evidence

The candidate binds version, attempt, candidate ref, exact commit, source tree,
policy, version manifest, toolchain, support, and evidence digests. An identical
repeat is idempotent. A different identity at the same candidate is mutation
and fails.

## Promotion evidence

Promotion requires an admitted candidate, matching commit and artifact digest,
canonical tag, signed and annotated intent, and exact single-ref push intent.
`rebuild=true`, fallback artifacts, unsigned/lightweight tags, all-tag pushes,
or a mismatched commit/digest fail before a provider can run.

## Troubleshooting

- `release version channel does not match` means the suffix and declared
  channel disagree; choose a new canonical version and render projections.
- `release mutation is forbidden in the main worktree` means the operator must
  start or resume an isolated release session.
- `beta backports accept reviewed bug fixes only` means the supplied change is
  not an admissible maintenance fix.
- `candidate identity is create-once` means inputs changed; allocate a new
  candidate attempt instead of overwriting the old one.
- `promotion must not rebuild` means return to candidate build/qualification;
  promotion is never a build retry.
- `withdrawal must preserve published release identity` means redeploy or
  publish a new correction rather than rewriting history.

## Verification boundary

Run this focused scenario once after changes, generate this mirror through
SPipe, scan it with `sspec-maintain`, and then run the release-bound whole suite
once. Required external rows stay blocked until their own receipts exist.

## Scenarios

### Hardened Simple and Spipe software release

#### loads the canonical release policy and rejects stale version projections

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-002
# @req REQ-003
# @req REQ-004
# @req REQ-005
# @req REQ-006
# @req REQ-007
# @req REQ-008
# @req REQ-009
# @req REQ-010
# @req REQ-011
# @req REQ-012
# @req REQ-013
# @req REQ-014
# @req REQ-015
```

</details>

#### prepares an isolated beta release and rejects the main worktree

- Prepare an isolated beta release
   - Expected: validate_release_session(main_session).reason equals `release mutation is forbidden in the main worktree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare an isolated beta release")
val session = setup_release_fixture()
expect(validate_release_session(session).valid).to_be(true)
expect(check_beta_preparation(parse_release_version("1.4.0-beta.2"), session).valid).to_be(true)
val main_session = ReleaseSession(
    session_id: session.session_id,
    workspace_path: session.main_workspace_path,
    main_workspace_path: session.main_workspace_path,
    work_branch: session.work_branch,
    target_ref: session.target_ref,
    base_sha: session.base_sha,
    expected_target_sha: session.expected_target_sha,
    policy_sha256: session.policy_sha256
)
expect(validate_release_session(main_session).reason).to_equal("release mutation is forbidden in the main worktree")
```

</details>

#### admits reviewed bug-fix backports and rejects unrelated features

- Admit reviewed bug-fix backports
   - Expected: check_backport_admission(feature).reason equals `beta backports accept reviewed bug fixes only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit reviewed bug-fix backports")
val request = setup_backport_fixture()
expect(check_backport_admission(request).valid).to_be(true)
val feature = BackportRequest(
    source_commit_sha: request.source_commit_sha,
    change_id: request.change_id,
    work_id: request.work_id,
    change_kind: "feat",
    review_receipt_sha256: request.review_receipt_sha256,
    target_line: request.target_line,
    expected_target_sha: request.expected_target_sha,
    adaptation_reason: request.adaptation_reason,
    evidence_sha256: request.evidence_sha256,
    result_commit_sha: request.result_commit_sha
)
expect(check_backport_admission(feature).reason).to_equal("beta backports accept reviewed bug fixes only")
```

</details>

#### freezes one complete candidate and rejects mutation

- Freeze and qualify the release candidate
   - Expected: check_candidate_create_once("different-existing-identity", candidate).reason equals `candidate identity is create-once and cannot be mutated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Freeze and qualify the release candidate")
val candidate = setup_candidate_fixture()
expect(check_candidate_manifest(candidate).valid).to_be(true)
val identity = candidate_identity(candidate)
expect(check_candidate_create_once(identity, candidate).valid).to_be(true)
expect(check_candidate_create_once("different-existing-identity", candidate).reason).to_equal("candidate identity is create-once and cannot be mutated")
```

</details>

#### promotes exact admitted artifacts without rebuilding or fallback

- Promote exact admitted artifacts
   - Expected: check_promotion_plan(admission, rebuild).reason equals `promotion must not rebuild admitted artifacts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Promote exact admitted artifacts")
val candidate = setup_candidate_fixture()
val admission = ReleaseAdmission(
    candidate_identity: candidate_identity(candidate),
    candidate_commit_sha: candidate.commit_sha,
    artifact_manifest_sha256: "artifact-digest",
    evidence_manifest_sha256: candidate.evidence_manifest_sha256,
    admitted: true
)
val plan = PromotionPlan(
    tag: "v1.4.0-beta.2",
    target_commit_sha: candidate.commit_sha,
    candidate_commit_sha: candidate.commit_sha,
    artifact_manifest_sha256: "artifact-digest",
    admitted_artifact_manifest_sha256: "artifact-digest",
    signed_tag: true,
    annotated_tag: true,
    exact_tag_push: true,
    rebuild: false,
    fallback_artifact: false
)
expect(check_promotion_plan(admission, plan).valid).to_be(true)
val rebuild = PromotionPlan(
    tag: plan.tag,
    target_commit_sha: plan.target_commit_sha,
    candidate_commit_sha: plan.candidate_commit_sha,
    artifact_manifest_sha256: plan.artifact_manifest_sha256,
    admitted_artifact_manifest_sha256: plan.admitted_artifact_manifest_sha256,
    signed_tag: plan.signed_tag,
    annotated_tag: plan.annotated_tag,
    exact_tag_push: plan.exact_tag_push,
    rebuild: true,
    fallback_artifact: false
)
expect(check_promotion_plan(admission, rebuild).reason).to_equal("promotion must not rebuild admitted artifacts")
```

</details>

#### withdraws without rewriting published release identity

- Withdraw without rewriting release identity
   - Expected: check_withdrawal_plan(true, false, false, "1.3.9").reason equals `withdrawal must preserve published release identity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Withdraw without rewriting release identity")
expect(check_withdrawal_plan(false, false, false, "1.3.9").valid).to_be(true)
expect(check_withdrawal_plan(true, false, false, "1.3.9").reason).to_equal("withdrawal must preserve published release identity")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/release_process_hardening.md`
- **Plan:** `doc/03_plan/sys_test/release_process_hardening.md`
- **Design:** `doc/05_design/release_process_hardening.md`
- **Research:** `doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-011`
- `REQ-012`
- `REQ-013`
- `REQ-014`
- `REQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `49abfa37e49d0d3ece9f4031752bd6af0bf67560e18be7c7fed2a338ccbbd6cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49abfa37e49d0d3ece9f4031752bd6af0bf67560e18be7c7fed2a338ccbbd6cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49abfa37e49d0d3ece9f4031752bd6af0bf67560e18be7c7fed2a338ccbbd6cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/app/release/feature/release_process_hardening_spec.spl
mirror: doc/06_spec/03_system/app/release/feature/release_process_hardening_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=65
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/release/feature/release_process_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/release/feature/release_process_hardening_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/app/release/feature/release_process_hardening_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/release/feature/release_process_hardening_spec.spl:164:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'loads the canonical release policy and rejects stale version projections' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/release/feature/release_process_hardening_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepares an isolated beta release and rejects the main worktree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/release/feature/release_process_hardening_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits reviewed bug-fix backports and rejects unrelated features' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/release/feature/release_process_hardening_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes one complete candidate and rejects mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
