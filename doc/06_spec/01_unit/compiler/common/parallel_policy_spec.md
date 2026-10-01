# Parallel Policy Specification

> Tests covering ResolvedParallelPolicyV1, ResolvedMemoryPolicyV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parallel Policy Specification

## Scenarios

### ResolvedParallelPolicyV1

#### pins the critical overlay to fail closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pins the critical overlay to fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the critical overlay to fail closed")
val critical = ResolvedParallelPolicyV1.for_assurance(AssuranceStrictness.Critical)
assert_equal(existing_parent_move_policy_to_u8(critical.parent_to_child_existing),
    existing_parent_move_policy_to_u8(ExistingParentMovePolicy.Deny))
assert_true(critical.require_bounded_mailbox)
assert_true(critical.require_deterministic_commit)
assert_true(critical.deny_dynamic_transport)
assert_true(critical.require_frozen_layout_receipt)
```

</details>

#### does not let a candidate weaken a project policy

- does not let a candidate weaken a project policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not let a candidate weaken a project policy")
val project = ResolvedParallelPolicyV1.for_assurance(AssuranceStrictness.Critical)
val candidate = ResolvedParallelPolicyV1.balanced()
val resolved = resolve_parallel_policy(project, candidate)
assert_true(resolved.is_at_least_as_strict_as(project))
assert_equal(existing_parent_move_policy_to_u8(resolved.parent_to_child_existing),
    existing_parent_move_policy_to_u8(ExistingParentMovePolicy.Deny))
```

</details>

### ResolvedMemoryPolicyV1

#### pins critical layout conversion and receipt requirements

- pins critical layout conversion and receipt requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins critical layout conversion and receipt requirements")
val critical = ResolvedMemoryPolicyV1.for_assurance(AssuranceStrictness.Critical)
assert_true(critical.require_bounded_buffer_bytes)
assert_true(critical.pin_address_observed_layout)
assert_true(critical.pin_external_abi_layout)
assert_true(critical.deny_implicit_layout_conversion)
assert_true(critical.require_frozen_layout_receipt)
```

</details>

#### merges memory constraints without weakening the project profile

- merges memory constraints without weakening the project profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges memory constraints without weakening the project profile")
val project = ResolvedMemoryPolicyV1.for_assurance(AssuranceStrictness.Critical)
val candidate = ResolvedMemoryPolicyV1.balanced()
val resolved = resolve_memory_policy(project, candidate)
assert_true(resolved.is_at_least_as_strict_as(project))
assert_true(resolved.deny_implicit_layout_conversion)
assert_true(resolved.require_frozen_layout_receipt)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/common/parallel_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ResolvedParallelPolicyV1, ResolvedMemoryPolicyV1.
- ResolvedParallelPolicyV1
- ResolvedMemoryPolicyV1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `752be86d7ed4d656414e583ce32b7855add79e2c349135f7051cd4326de7d4b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `752be86d7ed4d656414e583ce32b7855add79e2c349135f7051cd4326de7d4b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `752be86d7ed4d656414e583ce32b7855add79e2c349135f7051cd4326de7d4b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/common/parallel_policy_spec.spl
mirror: doc/06_spec/01_unit/compiler/common/parallel_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/common/parallel_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/common/parallel_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/common/parallel_policy_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the critical overlay to fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/parallel_policy_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not let a candidate weaken a project policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/parallel_policy_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins critical layout conversion and receipt requirements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
