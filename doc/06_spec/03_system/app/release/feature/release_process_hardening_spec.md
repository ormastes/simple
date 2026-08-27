# Protected beta and stable software release

> This manual shows a release operator how Simple and Spipe validate a beta or stable release before any VCS, build, signing, or hosting provider mutates external state. The executable scenarios exercise pure plans only. A local PASS does not claim that GitHub rulesets, signing keys, protected pushes, immutable publication, or registries were changed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

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
| Updated | 2026-08-27 |
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
simple release self-review-plan
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

Protected convergence additionally binds every selected main source SHA to one
result reachable in the pre-merge release inventory. Source and result must
have the same stable patch ID and share the exact release PR review/check
receipt; candidate admission independently replays every binding.

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
- `no exact self-attested review evidence` means review the server-current
  target/head/base/diff and redispatch; never label it independently
  authenticated, reuse expired evidence, or claim provider Approve.

## Verification boundary

Run this focused scenario once after changes, generate this mirror through
SPipe, scan it with `sspec-maintain`, and then run the release-bound whole suite
once. Required external rows stay blocked until their own receipts exist.

## Scenarios

### Hardened Simple and Spipe software release

#### loads the canonical release policy and rejects stale version projections

- Load the canonical release policy
   - Expected: beta.canonical equals `1.4.0-beta.2`
   - Expected: beta.line equals `1.4`
   - Expected: check_version_projection(beta.canonical, "VERSION", "1.4.0-beta.1").reason equals `version projection is stale: VERSION`
   - Expected: parse_release_version("1.4.0-BETA").channel equals `invalid`
   - Expected: parse_release_version("v1.4.0-beta.2").channel equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the canonical release policy")
val beta = parse_release_version("1.4.0-beta.2")
expect(beta.canonical).to_equal("1.4.0-beta.2")
expect(beta.line).to_equal("1.4")
expect(check_version_channel(beta, "beta").valid).to_be(true)
expect(check_version_projection(beta.canonical, "VERSION", "1.4.0-beta.1").reason).to_equal("version projection is stale: VERSION")
expect(parse_release_version("1.4.0-BETA").channel).to_equal("invalid")
expect(parse_release_version("v1.4.0-beta.2").channel).to_equal("invalid")
```

</details>

#### prepares an isolated beta release and rejects the main worktree

- Prepare an isolated beta release
   - Expected: validate_release_session(main_session).reason equals `release mutation is forbidden in the main worktree`
   - Expected: validate_release_session(unsafe_branch).reason equals `release session must own a work branch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
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
val unsafe_branch = ReleaseSession(
    session_id: session.session_id,
    workspace_path: session.workspace_path,
    main_workspace_path: session.main_workspace_path,
    work_branch: "work/release/../../main",
    target_ref: session.target_ref,
    base_sha: session.base_sha,
    expected_target_sha: session.expected_target_sha,
    policy_sha256: session.policy_sha256
)
expect(validate_release_session(unsafe_branch).reason).to_equal("release session must own a work branch")
```

</details>

#### admits reviewed bug-fix backports and rejects unrelated features

- Admit reviewed bug-fix backports
   - Expected: check_backport_admission(feature).reason equals `beta backports accept reviewed bug fixes only`
   - Expected: check_backport_admission(stale_review).reason equals `backport review receipt binding does not match the requested change`
   - Expected: check_backport_admission(missing_forward_port).reason equals `release-first emergency fix requires an exact forward-port receipt to main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 87 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit reviewed bug-fix backports")
val request = setup_backport_fixture()
expect(check_backport_admission(request).valid).to_be(true)
val feature = BackportRequest(
    direction: request.direction,
    source_ref: request.source_ref,
    source_commit_sha: request.source_commit_sha,
    change_id: request.change_id,
    work_id: request.work_id,
    change_kind: "feat",
    review_receipt_sha256: request.review_receipt_sha256,
    reviewed_source_commit_sha: request.reviewed_source_commit_sha,
    reviewed_change_id: request.reviewed_change_id,
    target_line: request.target_line,
    expected_target_sha: request.expected_target_sha,
    adaptation_reason: request.adaptation_reason,
    evidence_sha256: request.evidence_sha256,
    evidence_result_commit_sha: request.evidence_result_commit_sha,
    evidence_target_sha: request.evidence_target_sha,
    result_commit_sha: request.result_commit_sha,
    forward_port_target_ref: request.forward_port_target_ref,
    forward_port_receipt_sha256: request.forward_port_receipt_sha256
)
expect(check_backport_admission(feature).reason).to_equal("beta backports accept reviewed bug fixes only")
val stale_review = BackportRequest(
    direction: request.direction,
    source_ref: request.source_ref,
    source_commit_sha: request.source_commit_sha,
    change_id: request.change_id,
    work_id: request.work_id,
    change_kind: request.change_kind,
    review_receipt_sha256: request.review_receipt_sha256,
    reviewed_source_commit_sha: sha_b(),
    reviewed_change_id: request.reviewed_change_id,
    target_line: request.target_line,
    expected_target_sha: request.expected_target_sha,
    adaptation_reason: request.adaptation_reason,
    evidence_sha256: request.evidence_sha256,
    evidence_result_commit_sha: request.evidence_result_commit_sha,
    evidence_target_sha: request.evidence_target_sha,
    result_commit_sha: request.result_commit_sha,
    forward_port_target_ref: request.forward_port_target_ref,
    forward_port_receipt_sha256: request.forward_port_receipt_sha256
)
expect(check_backport_admission(stale_review).reason).to_equal("backport review receipt binding does not match the requested change")
val emergency = BackportRequest(
    direction: "beta_to_main",
    source_ref: request.target_line,
    source_commit_sha: request.source_commit_sha,
    change_id: request.change_id,
    work_id: request.work_id,
    change_kind: request.change_kind,
    review_receipt_sha256: request.review_receipt_sha256,
    reviewed_source_commit_sha: request.reviewed_source_commit_sha,
    reviewed_change_id: request.reviewed_change_id,
    target_line: request.target_line,
    expected_target_sha: request.expected_target_sha,
    adaptation_reason: "emergency correction originated on the beta line",
    evidence_sha256: request.evidence_sha256,
    evidence_result_commit_sha: request.evidence_result_commit_sha,
    evidence_target_sha: request.evidence_target_sha,
    result_commit_sha: request.result_commit_sha,
    forward_port_target_ref: "main",
    forward_port_receipt_sha256: digest_c()
)
expect(check_backport_admission(emergency).valid).to_be(true)
val missing_forward_port = BackportRequest(
    direction: emergency.direction,
    source_ref: emergency.source_ref,
    source_commit_sha: emergency.source_commit_sha,
    change_id: emergency.change_id,
    work_id: emergency.work_id,
    change_kind: emergency.change_kind,
    review_receipt_sha256: emergency.review_receipt_sha256,
    reviewed_source_commit_sha: emergency.reviewed_source_commit_sha,
    reviewed_change_id: emergency.reviewed_change_id,
    target_line: emergency.target_line,
    expected_target_sha: emergency.expected_target_sha,
    adaptation_reason: emergency.adaptation_reason,
    evidence_sha256: emergency.evidence_sha256,
    evidence_result_commit_sha: emergency.evidence_result_commit_sha,
    evidence_target_sha: emergency.evidence_target_sha,
    result_commit_sha: emergency.result_commit_sha,
    forward_port_target_ref: "main",
    forward_port_receipt_sha256: ""
)
expect(check_backport_admission(missing_forward_port).reason).to_equal("release-first emergency fix requires an exact forward-port receipt to main")
```

</details>

#### plans reviewed bidirectional convergence without mutating or repointing main

- Reconcile reviewed fixes with main
   - Expected: backport_plan.mutation equals `none`
   - Expected: forward_plan.forward_port_target_ref equals `main`
- Admit only an exhaustive receipt-bound release-first classification
   - Expected: check_convergence_admission(concealed).reason equals `every release-first inventory commit requires an exhaustive receipt-bound cla... (full value in folded executable source)`
   - Expected: plan_release_main_convergence(unsafe_tracking).reason equals `main must remain an independent trunk and never track a release branch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 82 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reconcile reviewed fixes with main")
val main_fix = ReviewedBugFix(
    commit_sha: sha_a(), review_receipt_sha256: digest_a(),
    source_ref: "main", change_kind: "fix"
)
val backport = ConvergenceRequest(
    last_scanned_main_sha: sha_b(), current_main_sha: sha_c(),
    release_ref: "release/1.4", release_head_sha: sha_b(),
    last_scan_epoch_seconds: 100, current_epoch_seconds: 200,
    scan_interval_seconds: 60, eligible_reviewed_bug_fixes: [main_fix],
    selected_bug_fix_shas: [sha_a()], caller_selection_confirmed: true,
    direction: "main_to_release", forward_port_required: false,
    forward_port_target_ref: "", main_tracks_release: false
)
val backport_plan = plan_release_main_convergence(backport)
expect(backport_plan.valid).to_be(true)
expect(backport_plan.ready).to_be(true)
expect(backport_plan.mutation).to_equal("none")
expect(backport_plan.main_remains_independent).to_be(true)

val release_fix = ReviewedBugFix(
    commit_sha: sha_a(), review_receipt_sha256: digest_b(),
    source_ref: "release/1.4", change_kind: "fix"
)
val forward_port = ConvergenceRequest(
    last_scanned_main_sha: sha_b(), current_main_sha: sha_c(),
    release_ref: "release/1.4", release_head_sha: sha_b(),
    last_scan_epoch_seconds: 100, current_epoch_seconds: 200,
    scan_interval_seconds: 60, eligible_reviewed_bug_fixes: [release_fix],
    selected_bug_fix_shas: [sha_a()], caller_selection_confirmed: true,
    direction: "release_to_main", forward_port_required: true,
    forward_port_target_ref: "main", main_tracks_release: false
)
val forward_plan = plan_release_main_convergence(forward_port)
expect(forward_plan.valid).to_be(true)
expect(forward_plan.forward_port_required).to_be(true)
expect(forward_plan.forward_port_target_ref).to_equal("main")

step("Admit only an exhaustive receipt-bound release-first classification")
val convergence_admission = ConvergenceAdmissionRequest(
    candidate_commit_sha: sha_c(), receipt_candidate_commit_sha: sha_c(),
    release_ref: "release/1.4", main_head_sha: sha_a(), release_head_sha: sha_c(),
    receipt_sha256: digest_a(), review_summary_sha256: digest_b(),
    evidence_receipt_sha256: digest_c(), integration_receipt_sha256: digest_d(),
    inventory_origin: "protected_integration", graph_independent: true,
    main_to_release_inventory_shas: [], main_to_release_shared_fix_shas: [],
    main_to_release_selected_shas: [], main_to_release_backported_shas: [],
    main_to_release_backport_result_shas: [], main_to_release_backport_target_refs: [],
    backport_receipt_sha256s: [], release_to_main_inventory_shas: [sha_b()],
    release_to_main_classified_shas: [sha_b()],
    release_to_main_classification_kinds: ["fix"],
    release_to_main_classification_receipt_sha256s: [digest_e()],
    release_to_main_forward_ported_shas: [sha_b()],
    release_to_main_forward_port_result_shas: [sha_a()],
    release_to_main_forward_port_target_refs: ["main"],
    forward_port_receipt_sha256s: [digest_f()]
)
expect(check_convergence_admission(convergence_admission).valid).to_be(true)
var concealed = convergence_admission
concealed.release_to_main_classified_shas = []
concealed.release_to_main_classification_kinds = []
concealed.release_to_main_classification_receipt_sha256s = []
concealed.release_to_main_forward_ported_shas = []
concealed.release_to_main_forward_port_result_shas = []
concealed.release_to_main_forward_port_target_refs = []
concealed.forward_port_receipt_sha256s = []
expect(check_convergence_admission(concealed).reason).to_equal("every release-first inventory commit requires an exhaustive receipt-bound classification")

val unsafe_tracking = ConvergenceRequest(
    last_scanned_main_sha: backport.last_scanned_main_sha,
    current_main_sha: backport.current_main_sha,
    release_ref: backport.release_ref,
    release_head_sha: backport.release_head_sha,
    last_scan_epoch_seconds: backport.last_scan_epoch_seconds,
    current_epoch_seconds: backport.current_epoch_seconds,
    scan_interval_seconds: backport.scan_interval_seconds,
    eligible_reviewed_bug_fixes: [], selected_bug_fix_shas: [],
    caller_selection_confirmed: false, direction: backport.direction,
    forward_port_required: false, forward_port_target_ref: "",
    main_tracks_release: true
)
expect(plan_release_main_convergence(unsafe_tracking).reason).to_equal("main must remain an independent trunk and never track a release branch")
```

</details>

#### admits exact-state self-attested review without claiming independent approval

- Self-attest the exact protected PR head/base/diff with the scoped gate
   - Expected: decision.head_sha equals `sha_a()`
   - Expected: decision.review_evidence_mode equals `self_attested`
- Reject stale and secret-bearing evidence before the provider check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Self-attest the exact protected PR head/base/diff with the scoped gate")
val policy = parse_self_review_policy_db(setup_self_review_policy())
val manifest = parse_self_review_changed_manifest(setup_self_review_manifest())
val decision = evaluate_self_review(policy, manifest, setup_self_review_request(policy.sha256))
expect(decision.allowed).to_be(true)
expect(decision.head_sha).to_equal(sha_a())
expect(decision.review_evidence_mode).to_equal("self_attested")
expect(decision.provider_action).to_contain("separate_eligible_broker")
expect(decision.provider_approval_claimed).to_be(false)

step("Reject stale and secret-bearing evidence before the provider check")
var stale = setup_self_review_request(policy.sha256)
stale.head_sha = sha_b()
expect(evaluate_self_review(policy, manifest, stale).allowed).to_be(false)
val secret_manifest = parse_self_review_changed_manifest(
    setup_self_review_manifest().replace("semantic_class: ordinary", "semantic_class: credential_secret")
)
expect(evaluate_self_review(policy, secret_manifest, setup_self_review_request(policy.sha256)).allowed).to_be(false)
```

</details>

#### freezes one complete candidate and rejects mutation

- Freeze and qualify the release candidate
   - Expected: identity.len() equals `64`
   - Expected: check_candidate_create_once("different-existing-identity", candidate).reason equals `candidate identity is create-once and cannot be mutated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Freeze and qualify the release candidate")
val candidate = setup_candidate_fixture()
expect(check_candidate_manifest(candidate).valid).to_be(true)
val identity = candidate_identity(candidate)
expect(identity.len()).to_equal(64)
expect(check_candidate_create_once(identity, candidate).valid).to_be(true)
expect(check_candidate_create_once("different-existing-identity", candidate).reason).to_equal("candidate identity is create-once and cannot be mutated")
val separator_candidate = CandidateManifest(
    version: candidate.version,
    attempt: candidate.attempt,
    candidate_ref: candidate.candidate_ref,
    commit_sha: sha_b(),
    source_tree_sha256: digest_a(),
    policy_sha256: candidate.policy_sha256,
    version_manifest_sha256: candidate.version_manifest_sha256,
    toolchain_manifest_sha256: candidate.toolchain_manifest_sha256,
    support_manifest_sha256: candidate.support_manifest_sha256,
    build_graph_sha256: candidate.build_graph_sha256,
    creator_identity: candidate.creator_identity,
    evidence_manifest_sha256: candidate.evidence_manifest_sha256
)
expect(candidate_identity(separator_candidate) == identity).to_be(false)
val qualification = QualificationReceipt(
    candidate_identity: identity,
    candidate_commit_sha: candidate.commit_sha,
    build_graph_sha256: candidate.build_graph_sha256,
    artifact_manifest_sha256: digest_b(),
    evidence_manifest_sha256: candidate.evidence_manifest_sha256,
    required_support_sha256: digest_c(),
    required_support_passed: true
)
expect(check_qualification_receipt(candidate, qualification).valid).to_be(true)
```

</details>

#### promotes exact admitted artifacts without rebuilding or fallback

- Promote exact admitted artifacts
   - Expected: check_promotion_plan(admission, rebuild).reason equals `promotion must not rebuild admitted artifacts`
   - Expected: check_promotion_plan(admission, stale_candidate).reason equals `promotion candidate identity does not match release admission`
   - Expected: check_promotion_plan(admission, wrong_version).reason equals `promotion tag version does not match the admitted candidate version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Promote exact admitted artifacts")
val candidate = setup_candidate_fixture()
val admission = ReleaseAdmission(
    candidate_version: candidate.version,
    candidate_attempt: candidate.attempt,
    candidate_ref: candidate.candidate_ref,
    candidate_identity: candidate_identity(candidate),
    candidate_commit_sha: candidate.commit_sha,
    source_tree_sha256: candidate.source_tree_sha256,
    policy_sha256: candidate.policy_sha256,
    version_manifest_sha256: candidate.version_manifest_sha256,
    toolchain_manifest_sha256: candidate.toolchain_manifest_sha256,
    support_manifest_sha256: candidate.support_manifest_sha256,
    build_graph_sha256: candidate.build_graph_sha256,
    creator_identity: candidate.creator_identity,
    artifact_manifest_sha256: digest_a(),
    evidence_manifest_sha256: candidate.evidence_manifest_sha256,
    qualification_receipt_sha256: digest_b(),
    admission_receipt_schema: "spipe-review-admission/1",
    admission_receipt_sha256: digest_c()
)
val plan = PromotionPlan(
    candidate_identity: admission.candidate_identity,
    tag: "v1.4.0-beta.2",
    target_commit_sha: candidate.commit_sha,
    candidate_commit_sha: candidate.commit_sha,
    artifact_manifest_sha256: digest_a(),
    admitted_artifact_manifest_sha256: digest_a(),
    signed_tag: true,
    annotated_tag: true,
    exact_tag_push: true,
    rebuild: false,
    fallback_artifact: false
)
expect(check_promotion_plan(admission, plan).valid).to_be(true)
var self_review_only = admission
self_review_only.admission_receipt_schema = "spipe-self-review-decision/1"
expect(check_promotion_plan(self_review_only, plan).reason).to_contain("self-review decisions cannot authorize")
val rebuild = PromotionPlan(
    candidate_identity: plan.candidate_identity,
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
val stale_candidate = PromotionPlan(
    candidate_identity: "stale-candidate-identity",
    tag: plan.tag,
    target_commit_sha: plan.target_commit_sha,
    candidate_commit_sha: plan.candidate_commit_sha,
    artifact_manifest_sha256: plan.artifact_manifest_sha256,
    admitted_artifact_manifest_sha256: plan.admitted_artifact_manifest_sha256,
    signed_tag: plan.signed_tag,
    annotated_tag: plan.annotated_tag,
    exact_tag_push: plan.exact_tag_push,
    rebuild: false,
    fallback_artifact: false
)
expect(check_promotion_plan(admission, stale_candidate).reason).to_equal("promotion candidate identity does not match release admission")
val wrong_version = PromotionPlan(
    candidate_identity: plan.candidate_identity,
    tag: "v1.4.0-beta.3",
    target_commit_sha: plan.target_commit_sha,
    candidate_commit_sha: plan.candidate_commit_sha,
    artifact_manifest_sha256: plan.artifact_manifest_sha256,
    admitted_artifact_manifest_sha256: plan.admitted_artifact_manifest_sha256,
    signed_tag: plan.signed_tag,
    annotated_tag: plan.annotated_tag,
    exact_tag_push: plan.exact_tag_push,
    rebuild: false,
    fallback_artifact: false
)
expect(check_promotion_plan(admission, wrong_version).reason).to_equal("promotion tag version does not match the admitted candidate version")
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
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/release_process_hardening.md`
- **Plan:** `doc/03_plan/sys_test/release_process_hardening.md`
- **Design:** `doc/05_design/release_process_hardening.md`
- **Research:** `doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`


</details>
