# Storage Simd Schedule Specification

> Tests covering storage SIMD full-block schedule.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Simd Schedule Specification

## Scenarios

### storage SIMD full-block schedule

#### represents an empty array without issuing a vector block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- represents an empty array without issuing a vector block


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("represents an empty array without issuing a vector block")
val schedule = storage_simd_schedule(
    admitted_eight_lane_f32(), 0, 64, 0, 0)
assert_true(schedule.valid)
assert_equal(schedule.tail_mode, StorageSimdTailMode.Empty)
assert_equal(schedule.full_block_count, 0)
assert_equal(schedule.physical_block_count, 0)
assert_equal(schedule.required_bytes, 0)
```

</details>

#### schedules exact multiples as full blocks only

- schedules exact multiples as full blocks only


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("schedules exact multiples as full blocks only")
val schedule = storage_simd_schedule(
    admitted_eight_lane_f32(), 16, 64, 128, 2)
assert_true(schedule.valid)
assert_equal(schedule.full_block_count, 2)
assert_equal(schedule.physical_block_count, 2)
assert_equal(schedule.tail_count, 0)
assert_equal(schedule.tail_start, 16)
assert_equal(schedule.required_bytes, 128)
assert_equal(schedule.tail_mode, StorageSimdTailMode.FullBlocksOnly)
```

</details>

#### keeps a ninth element in an explicit scalar tail

- keeps a ninth element in an explicit scalar tail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a ninth element in an explicit scalar tail")
val schedule = storage_simd_schedule(
    admitted_eight_lane_f32(), 9, 64, 128, 2)
assert_true(schedule.valid)
assert_equal(schedule.full_block_count, 1)
assert_equal(schedule.physical_block_count, 2)
assert_equal(schedule.tail_count, 1)
assert_equal(schedule.tail_start, 8)
assert_equal(schedule.tail_mode, StorageSimdTailMode.ScalarTail)
assert_equal(schedule.reason, "scalar-tail-required")
```

</details>

#### uses only a scalar tail when the array is smaller than one block

- uses only a scalar tail when the array is smaller than one block


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses only a scalar tail when the array is smaller than one block")
val schedule = storage_simd_schedule(
    admitted_eight_lane_f32(), 7, 64, 64, 1)
assert_true(schedule.valid)
assert_equal(schedule.full_block_count, 0)
assert_equal(schedule.physical_block_count, 1)
assert_equal(schedule.tail_count, 7)
assert_equal(schedule.tail_start, 0)
assert_equal(schedule.tail_mode, StorageSimdTailMode.ScalarTail)
```

</details>

#### rejects invalid inputs block budgets capacity and overflow

- rejects invalid inputs block budgets capacity and overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid inputs block budgets capacity and overflow")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), -1, 64, 64, 1).reason,
    "invalid-schedule-input")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 8, -1, 64, 1).reason,
    "invalid-schedule-input")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 8, 64, -1, 1).reason,
    "invalid-schedule-input")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 8, 64, 64, -1).reason,
    "invalid-schedule-input")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 9, 64, 128, 1).reason,
    "block-budget-exceeded")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 9, 64, 127, 2).reason,
    "physical-capacity-too-small")
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 8,
    9223372036854775807, 9223372036854775807, 1).required_bytes,
    9223372036854775807)
assert_equal(storage_simd_schedule(
    admitted_eight_lane_f32(), 16,
    9223372036854775807, 9223372036854775807, 2).reason,
    "required-bytes-overflow")
```

</details>

#### refuses fallback scalable and rejected admissions

- refuses fallback scalable and rejected admissions


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses fallback scalable and rejected admissions")
val aos = storage_layout_plan_v1(51, StorageLayoutKind.AoS, 1, 8,
    false, StorageConversionPolicy.Never, "simd-policy", "reference")
val fallback = storage_simd_admit(
    aos, 32, 8, VectorWidthRouter.x86_64_avx2())
assert_equal(storage_simd_schedule(
    fallback, 8, 64, 64, 1).reason,
    "scalar-fallback-has-no-simd-schedule")
val aosoa = storage_layout_plan_v1(51, StorageLayoutKind.AoSoA, 8, 32,
    false, StorageConversionPolicy.Cached, "simd-policy", "simd-block")
val scalable = storage_simd_admit(
    aosoa, 32, 8, VectorWidthRouter.aarch64_sve(256))
assert_equal(storage_simd_schedule(
    scalable, 8, 64, 64, 1).reason,
    "scalable-schedule-deferred")
val rejected = storage_simd_admit(
    aosoa, 32, 8, VectorWidthRouter.x86_64_sse2())
assert_equal(storage_simd_schedule(
    rejected, 8, 64, 64, 1).reason,
    "simd-admission-rejected")
val forged = storage_simd_admission_v1(
    StorageSimdAdmissionKind.AdmittedFixed, 8, 130, "forged")
assert_equal(storage_simd_schedule(
    forged, 8, 64, 64, 1).reason,
    "invalid-admission-shape")
val zero_lanes = storage_simd_admission_v1(
    StorageSimdAdmissionKind.AdmittedFixed, 0, 128, "forged")
assert_equal(storage_simd_schedule(
    zero_lanes, 8, 64, 64, 1).reason,
    "invalid-admission-shape")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering storage SIMD full-block schedule.
- storage SIMD full-block schedule

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `0759b2fa699f80effc689079b36cfb313f571cc0edaf98ba83a4b388a8d32c8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0759b2fa699f80effc689079b36cfb313f571cc0edaf98ba83a4b388a8d32c8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0759b2fa699f80effc689079b36cfb313f571cc0edaf98ba83a4b388a8d32c8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/storage_simd_schedule_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_schedule_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_schedule_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'represents an empty array without issuing a vector block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'schedules exact multiples as full blocks only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a ninth element in an explicit scalar tail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
