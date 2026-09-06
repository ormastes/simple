# Promotion Specification

> Tests covering Eligibility gate (§15.1), Merge strategy consequences (§15.3), via a local fake ancestry oracle, Stale/unauthenticated snapshot cannot authorize promotion (§15.1), Remote read/write policy matrix (§15.4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Promotion Specification

## Scenarios

### Eligibility gate (§15.1)

#### accepts an input where every condition passes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an input where every condition passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an input where every condition passes")
val input = eligibility_input_all_pass(sample_receipt())
val result = eligibility_check(input)
match result:
    case EligibilityResult.Eligible:
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects a dirty tree as CleanSourceTree

- rejects a dirty tree as CleanSourceTree


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a dirty tree as CleanSourceTree")
var input = eligibility_input_all_pass(sample_receipt())
input.clean_tree = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.CleanSourceTree):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects a non-exact commit as ExactImmutableSourceCommit

- rejects a non-exact commit as ExactImmutableSourceCommit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-exact commit as ExactImmutableSourceCommit")
var input = eligibility_input_all_pass(sample_receipt())
input.exact_commit_pinned = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.ExactImmutableSourceCommit):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects unauthenticated repository identity

- rejects unauthenticated repository identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unauthenticated repository identity")
var input = eligibility_input_all_pass(sample_receipt())
input.repository_identity_authenticated = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.AuthenticatedRepositoryIdentity):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects an untrusted origin/main snapshot

- rejects an untrusted origin/main snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an untrusted origin/main snapshot")
var input = eligibility_input_all_pass(sample_receipt())
input.origin_main_snapshot_trusted = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.TrustedOriginMainSnapshot):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects a stale origin/main snapshot even if marked trusted

- rejects a stale origin/main snapshot even if marked trusted


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a stale origin/main snapshot even if marked trusted")
var input = eligibility_input_all_pass(sample_receipt())
input.origin_main_snapshot_fresh = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.TrustedOriginMainSnapshot):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects a commit not reachable from the snapshot

- rejects a commit not reachable from the snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a commit not reachable from the snapshot")
var input = eligibility_input_all_pass(sample_receipt())
input.commit_reachable_from_snapshot = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.SourceCommitReachableFromSnapshot):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects an untrusted CI builder

- rejects an untrusted CI builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an untrusted CI builder")
var input = eligibility_input_all_pass(sample_receipt())
input.builder_is_trusted_ci = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.TrustedCiBuilderAndProtectedWorkflow):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects an unprotected workflow

- rejects an unprotected workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unprotected workflow")
var input = eligibility_input_all_pass(sample_receipt())
input.workflow_is_protected = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.TrustedCiBuilderAndProtectedWorkflow):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects non-hermetic/undeclared inputs

- rejects non-hermetic/undeclared inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-hermetic/undeclared inputs")
var input = eligibility_input_all_pass(sample_receipt())
input.inputs_are_hermetic_and_declared = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.HermeticDeclaredActionInputs):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects unverified manifest/artifacts

- rejects unverified manifest/artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unverified manifest/artifacts")
var input = eligibility_input_all_pass(sample_receipt())
input.manifest_and_artifacts_strictly_verified = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.StrictManifestAndArtifactVerification):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects when required tests/proofs did not pass

- rejects when required tests/proofs did not pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when required tests/proofs did not pass")
var input = eligibility_input_all_pass(sample_receipt())
input.required_tests_or_proofs_passed = false
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.SuccessfulRequiredTestsOrProofs):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects a missing receipt

- rejects a missing receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a missing receipt")
var input = eligibility_input_all_pass(sample_receipt())
input.receipt = nil
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.SignedPromotionReceipt):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### rejects an unsigned receipt

- rejects an unsigned receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsigned receipt")
var input = eligibility_input_all_pass(sample_receipt())
var r = sample_receipt()
r.signature = ""
input.receipt = r
match eligibility_check(input):
    case EligibilityResult.Rejected(EligibilityCondition.SignedPromotionReceipt):
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

### Merge strategy consequences (§15.3), via a local fake ancestry oracle

#### fast-forward merge: branch tip reachable -> promotable

- fast-forward merge: branch tip reachable -> promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast-forward merge: branch tip reachable -> promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-ff"])
val result = check_commit_reachable_from_main(oracle, "commit-ff", now)
assert_true(result.reachable)
```

</details>

#### normal merge commit: branch tip reachable -> promotable

- normal merge commit: branch tip reachable -> promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal merge commit: branch tip reachable -> promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-merge"])
val result = check_commit_reachable_from_main(oracle, "commit-merge", now)
assert_true(result.reachable)
```

</details>

#### rebase-then-fast-forward: OLD branch commit not reachable -> not promotable

- rebase-then-fast-forward: OLD branch commit not reachable -> not promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebase-then-fast-forward: OLD branch commit not reachable -> not promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-rebased-new"])
val result = check_commit_reachable_from_main(oracle, "commit-old-branch-tip", now)
assert_false(result.reachable)
```

</details>

#### squash merge: original branch commit not reachable -> not promotable

- squash merge: original branch commit not reachable -> not promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("squash merge: original branch commit not reachable -> not promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-squash-result"])
val result = check_commit_reachable_from_main(oracle, "commit-original-branch-tip", now)
assert_false(result.reachable)
```

</details>

#### cherry-pick: original commit not reachable -> not promotable

- cherry-pick: original commit not reachable -> not promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cherry-pick: original commit not reachable -> not promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-cherry-picked"])
val result = check_commit_reachable_from_main(oracle, "commit-original", now)
assert_false(result.reachable)
```

</details>

#### force-pushed main removing the commit: not reachable in new snapshot -> not promotable

- force-pushed main removing the commit: not reachable in new snapshot -> not promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("force-pushed main removing the commit: not reachable in new snapshot -> not promotable")
val now: i64 = 10000000
val oracle = FakeAncestryOracle(snapshot: fresh_snapshot(now), ancestors: ["commit-new-main-tip"])
val result = check_commit_reachable_from_main(oracle, "commit-removed-by-force-push", now)
assert_false(result.reachable)
```

</details>

### Stale/unauthenticated snapshot cannot authorize promotion (§15.1)

#### rejects even a truly-ancestor commit when the snapshot is stale

- rejects even a truly-ancestor commit when the snapshot is stale


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects even a truly-ancestor commit when the snapshot is stale")
val now: i64 = 100000000
val oracle = FakeAncestryOracle(snapshot: stale_snapshot(now), ancestors: ["commit-real-ancestor"])
val result = check_commit_reachable_from_main(oracle, "commit-real-ancestor", now)
assert_false(result.reachable)
assert_false(result.snapshot_fresh)
```

</details>

#### rejects an unauthenticated fetch even if timestamp looks fresh

- rejects an unauthenticated fetch even if timestamp looks fresh


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unauthenticated fetch even if timestamp looks fresh")
val now: i64 = 100000000
val oracle = FakeAncestryOracle(snapshot: unauthenticated_snapshot(now), ancestors: ["commit-real-ancestor"])
val result = check_commit_reachable_from_main(oracle, "commit-real-ancestor", now)
assert_false(result.reachable)
```

</details>

#### snapshot_is_fresh is false for a snapshot older than the max age

- snapshot_is_fresh is false for a snapshot older than the max age


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("snapshot_is_fresh is false for a snapshot older than the max age")
val now: i64 = 100000000
val snap = stale_snapshot(now)
assert_false(snapshot_is_fresh(snap, now))
```

</details>

#### snapshot_is_fresh is true for a just-fetched authenticated snapshot

- snapshot_is_fresh is true for a just-fetched authenticated snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("snapshot_is_fresh is true for a just-fetched authenticated snapshot")
val now: i64 = 100000000
val snap = fresh_snapshot(now)
assert_true(snapshot_is_fresh(snap, now))
```

</details>

### Remote read/write policy matrix (§15.4)

#### dirty developer worktree cannot write remote-main

- dirty developer worktree cannot write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dirty developer worktree cannot write remote-main")
assert_false(remote_write_main_allowed(ProducerClass.DirtyDeveloperWorktree))
```

</details>

#### clean developer branch cannot write remote-main

- clean developer branch cannot write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean developer branch cannot write remote-main")
assert_false(remote_write_main_allowed(ProducerClass.CleanDeveloperBranch))
```

</details>

#### untrusted PR/fork cannot write remote-main

- untrusted PR/fork cannot write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("untrusted PR/fork cannot write remote-main")
assert_false(remote_write_main_allowed(ProducerClass.UntrustedPullRequestOrFork))
```

</details>

#### trusted branch CI cannot write remote-main

- trusted branch CI cannot write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trusted branch CI cannot write remote-main")
assert_false(remote_write_main_allowed(ProducerClass.TrustedBranchCi))
```

</details>

#### trusted main CI CAN write remote-main

- trusted main CI CAN write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trusted main CI CAN write remote-main")
assert_true(remote_write_main_allowed(ProducerClass.TrustedMainCi))
```

</details>

#### release CI CAN write remote-main

- release CI CAN write remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("release CI CAN write remote-main")
assert_true(remote_write_main_allowed(ProducerClass.ReleaseCi))
```

</details>

#### every producer class can read remote-main

- every producer class can read remote-main


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every producer class can read remote-main")
assert_true(remote_read_main_allowed(ProducerClass.DirtyDeveloperWorktree))
assert_true(remote_read_main_allowed(ProducerClass.CleanDeveloperBranch))
assert_true(remote_read_main_allowed(ProducerClass.UntrustedPullRequestOrFork))
assert_true(remote_read_main_allowed(ProducerClass.TrustedBranchCi))
assert_true(remote_read_main_allowed(ProducerClass.TrustedMainCi))
assert_true(remote_read_main_allowed(ProducerClass.ReleaseCi))
```

</details>

#### only trusted branch CI can write the branch namespace

- only trusted branch CI can write the branch namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only trusted branch CI can write the branch namespace")
assert_true(remote_write_branch_allowed(ProducerClass.TrustedBranchCi))
assert_false(remote_write_branch_allowed(ProducerClass.DirtyDeveloperWorktree))
assert_false(remote_write_branch_allowed(ProducerClass.CleanDeveloperBranch))
assert_false(remote_write_branch_allowed(ProducerClass.TrustedMainCi))
```

</details>

#### the unconditional developer-machine guard holds for both developer classes

- the unconditional developer-machine guard holds for both developer classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the unconditional developer-machine guard holds for both developer classes")
assert_true(developer_machine_write_main_is_always_false(ProducerClass.DirtyDeveloperWorktree))
assert_true(developer_machine_write_main_is_always_false(ProducerClass.CleanDeveloperBranch))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache_v2/promotion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Eligibility gate (§15.1), Merge strategy consequences (§15.3), via a local fake ancestry oracle, Stale/unauthenticated snapshot cannot authorize promotion (§15.1), Remote read/write policy matrix (§15.4).
- Eligibility gate (§15.1)
- Merge strategy consequences (§15.3), via a local fake ancestry oracle
- Stale/unauthenticated snapshot cannot authorize promotion (§15.1)
- Remote read/write policy matrix (§15.4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe7eb23ac0ef9bbbfd9dd73b9a45c46cfe7c4e58da6bac2b47096ab0e9ff92ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe7eb23ac0ef9bbbfd9dd73b9a45c46cfe7c4e58da6bac2b47096ab0e9ff92ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe7eb23ac0ef9bbbfd9dd73b9a45c46cfe7c4e58da6bac2b47096ab0e9ff92ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/cache_v2/promotion_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache_v2/promotion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache_v2/promotion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache_v2/promotion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache_v2/promotion_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an input where every condition passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/promotion_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a dirty tree as CleanSourceTree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/promotion_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a non-exact commit as ExactImmutableSourceCommit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
