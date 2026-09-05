# Native Driver Avx2 Policy Specification

> Tests covering custom native driver AVX2 policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Driver Avx2 Policy Specification

## Scenarios

### custom native driver AVX2 policy

#### admits a requested host v3 profile only when runtime AVX2 is available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a requested host v3 profile only when runtime AVX2 is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a requested host v3 profile only when runtime AVX2 is available")
val admitted = backend_helper_target_opt_context("", "x86_64-v3", true)
assert_equal(admitted.x86_caps.has_avx2, true)
```

</details>

#### denies the same profile when runtime AVX2 is unavailable

- denies the same profile when runtime AVX2 is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies the same profile when runtime AVX2 is unavailable")
val denied = backend_helper_target_opt_context("", "x86_64-v3", false)
assert_equal(denied.x86_caps.has_avx2, false)
```

</details>

#### denies target-profile inference for cross compilation

- denies target-profile inference for cross compilation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies target-profile inference for cross compilation")
val denied = backend_helper_target_opt_context(
    "x86_64-unknown-linux-gnu", "x86_64-v3", true)
assert_equal(denied.x86_caps.has_avx2, false)
```

</details>

#### keeps baseline and unknown CPU profiles denied

- keeps baseline and unknown CPU profiles denied


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps baseline and unknown CPU profiles denied")
assert_equal(
    backend_helper_target_opt_context("", "x86_64-v2", true).x86_caps.has_avx2,
    false)
assert_equal(
    backend_helper_target_opt_context("", "unknown", true).x86_caps.has_avx2,
    false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering custom native driver AVX2 policy.
- custom native driver AVX2 policy

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

- Canonical SPipe generation for source `ea69d0b469622fcbed5d97557f74a85181b91eff7bd75241c022fe102cf98f94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea69d0b469622fcbed5d97557f74a85181b91eff7bd75241c022fe102cf98f94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea69d0b469622fcbed5d97557f74a85181b91eff7bd75241c022fe102cf98f94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a requested host v3 profile only when runtime AVX2 is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies the same profile when runtime AVX2 is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/native_driver_avx2_policy_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies target-profile inference for cross compilation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
