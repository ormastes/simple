# Storage Simd Admission Specification

> Tests covering storage SIMD admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Simd Admission Specification

## Scenarios

### storage SIMD admission

#### admits an AVX2-compatible eight-lane f32 AoSoA block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits an AVX2-compatible eight-lane f32 AoSoA block


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits an AVX2-compatible eight-lane f32 AoSoA block")
val plan = storage_layout_plan_v1(41, StorageLayoutKind.AoSoA, 8, 32,
    false, StorageConversionPolicy.Cached, "simd-policy", "simd-block")
val result = storage_simd_admit(
    plan, 32, 8, VectorWidthRouter.x86_64_avx2())
assert_equal(result.kind, StorageSimdAdmissionKind.AdmittedFixed)
assert_equal(result.lane_count, 8)
assert_equal(result.vector_bits, 256)
assert_equal(result.reason, "fixed-width-compatible")
```

</details>

#### rejects fixed-width overflow and a mismatched AoSoA block

- rejects fixed-width overflow and a mismatched AoSoA block


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fixed-width overflow and a mismatched AoSoA block")
val plan = storage_layout_plan_v1(41, StorageLayoutKind.AoSoA, 8, 32,
    false, StorageConversionPolicy.Cached, "simd-policy", "simd-block")
val too_wide = storage_simd_admit(
    plan, 32, 8, VectorWidthRouter.x86_64_sse2())
assert_equal(too_wide.kind, StorageSimdAdmissionKind.Rejected)
assert_equal(too_wide.reason, "fixed-width-too-wide")
val mismatch = storage_simd_admit(
    plan, 32, 4, VectorWidthRouter.x86_64_avx2())
assert_equal(mismatch.kind, StorageSimdAdmissionKind.Rejected)
assert_equal(mismatch.reason, "block-width-mismatch")
```

</details>

#### falls back for AoS and SoA without claiming SIMD lowering

- falls back for AoS and SoA without claiming SIMD lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back for AoS and SoA without claiming SIMD lowering")
val aos = storage_layout_plan_v1(41, StorageLayoutKind.AoS, 1, 8,
    false, StorageConversionPolicy.Never, "simd-policy", "reference")
val soa = storage_layout_plan_v1(41, StorageLayoutKind.SoA, 1, 8,
    false, StorageConversionPolicy.Cached, "simd-policy", "columns")
assert_equal(storage_simd_admit(
    aos, 32, 4, VectorWidthRouter.aarch64_neon()).kind,
    StorageSimdAdmissionKind.ScalarFallback)
assert_equal(storage_simd_admit(
    soa, 32, 4, VectorWidthRouter.aarch64_neon()).kind,
    StorageSimdAdmissionKind.ScalarFallback)
```

</details>

#### rejects pinned ABI storage and malformed widths

- rejects pinned ABI storage and malformed widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects pinned ABI storage and malformed widths")
val pinned = storage_layout_plan_v1(41, StorageLayoutKind.ExternalFixed,
    1, 8, true, StorageConversionPolicy.Pinned,
    "simd-policy", "external")
assert_equal(storage_simd_admit(
    pinned, 32, 4, VectorWidthRouter.aarch64_neon()).reason,
    "abi-layout-pinned")
val aosoa = storage_layout_plan_v1(41, StorageLayoutKind.AoSoA, 4, 16,
    false, StorageConversionPolicy.Cached, "simd-policy", "simd-block")
assert_equal(storage_simd_admit(
    aosoa, 7, 4, VectorWidthRouter.aarch64_neon()).reason,
    "invalid-element-width")
assert_equal(storage_simd_admit(
    aosoa, 64, 4611686018427387903,
    VectorWidthRouter.x86_64_avx512()).reason,
    "vector-width-overflow")
```

</details>

#### defers scalable SVE and RVV routes explicitly

- defers scalable SVE and RVV routes explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defers scalable SVE and RVV routes explicitly")
val plan = storage_layout_plan_v1(41, StorageLayoutKind.AoSoA, 4, 16,
    false, StorageConversionPolicy.Cached, "simd-policy", "simd-block")
val sve = storage_simd_admit(
    plan, 32, 4, VectorWidthRouter.aarch64_sve(128))
val rvv = storage_simd_admit(
    plan, 32, 4, VectorWidthRouter.riscv64_rvv(128))
assert_equal(sve.kind, StorageSimdAdmissionKind.DeferredScalable)
assert_equal(rvv.kind, StorageSimdAdmissionKind.DeferredScalable)
assert_equal(sve.reason, "scalable-native-lowering-deferred")
assert_equal(rvv.reason, "scalable-native-lowering-deferred")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering storage SIMD admission.
- storage SIMD admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `201544c11e141718b8f37281850e0c9bf7f7ec235b5bf3eb6025473b474a66b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `201544c11e141718b8f37281850e0c9bf7f7ec235b5bf3eb6025473b474a66b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `201544c11e141718b8f37281850e0c9bf7f7ec235b5bf3eb6025473b474a66b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/storage_simd_admission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits an AVX2-compatible eight-lane f32 AoSoA block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects fixed-width overflow and a mismatched AoSoA block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back for AoS and SoA without claiming SIMD lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
