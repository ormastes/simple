# Storage Simd Codegen Specification

> Tests covering storage SIMD typed MIR codegen.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Simd Codegen Specification

## Scenarios

### storage SIMD typed MIR codegen

#### emits typed f32x8 load binop and store for a proven full block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits typed f32x8 load binop and store for a proven full block


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits typed f32x8 load binop and store for a proven full block")
val result = emit(codegen_schedule(16), 1, "f32", "Add")
assert_true(result.ok)
assert_equal(result.instructions.len(), 4)
val first_is_load = match result.instructions[0].kind:
    case MirSimdLoad(dest, ptr, aligned, vec_type):
        dest.id == 10 and not aligned and vec_type.kind == MirTypeKind.Vec8f
    case _: false
val operation_is_add = match result.instructions[2].kind:
    case MirSimdBinop(dest, lhs, rhs, operation):
        dest.id == 12 and operation == "Add"
    case _: false
val last_is_store = match result.instructions[3].kind:
    case MirSimdStore(value, ptr, aligned): not aligned
    case _: false
assert_true(first_is_load)
assert_true(operation_is_add)
assert_true(last_is_store)
assert_equal(result.reason, "typed-full-block-emitted")
```

</details>

#### never emits a vector operation for a scalar tail block

- never emits a vector operation for a scalar tail block


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never emits a vector operation for a scalar tail block")
val schedule = codegen_schedule(9)
assert_equal(schedule.full_block_count, 1)
assert_equal(schedule.tail_count, 1)
val tail = emit(schedule, 1, "f32", "Add")
assert_false(tail.ok)
assert_equal(tail.reason, "block-is-not-a-full-vector-block")
```

</details>

#### refuses arrays with no full block

- refuses arrays with no full block


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses arrays with no full block")
val schedule = codegen_schedule(7)
assert_equal(schedule.full_block_count, 0)
val result = emit(schedule, 0, "f32", "Add")
assert_false(result.ok)
assert_equal(result.instructions.len(), 0)
assert_equal(result.reason, "block-is-not-a-full-vector-block")
```

</details>

#### supports only concrete MIR vector types and known operations

- supports only concrete MIR vector types and known operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports only concrete MIR vector types and known operations")
val schedule = codegen_schedule(8)
assert_equal(emit(schedule, 0, "f64", "Add").reason,
    "unsupported-vector-type")
assert_equal(emit(schedule, 0, "f32", "Pow").reason,
    "unsupported-vector-operation")
assert_equal(emit_for(
    schedule, 0, "f32", "Add", "native-x86_64").reason,
    "backend-has-no-typed-simd-lowering")
```

</details>

#### emits aligned f32x8 MIR only for a proven native AVX2 projection

- emits aligned f32x8 MIR only for a proven native AVX2 projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits aligned f32x8 MIR only for a proven native AVX2 projection")
val schedule = codegen_schedule(8)
val unproven = emit_for(schedule, 0, "f32", "Add", "native-x86_64-avx2")
assert_false(unproven.ok)
assert_equal(unproven.reason, "native-avx2-alignment-unproven")
val proven = emit_for(schedule, 0, "f32", "Add", "native-x86_64-avx2", true)
assert_true(proven.ok)
val aligned_load = match proven.instructions[0].kind:
    case MirSimdLoad(_, _, aligned, vec_type): aligned and vec_type.kind == MirTypeKind.Vec8f
    case _: false
assert_true(aligned_load)
```

</details>

#### rejects an invalid schedule before emitting MIR

- rejects an invalid schedule before emitting MIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid schedule before emitting MIR")
val empty = codegen_schedule(0)
val result = emit(empty, 0, "f32", "Add")
assert_false(result.ok)
assert_equal(result.reason, "block-is-not-a-full-vector-block")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering storage SIMD typed MIR codegen.
- storage SIMD typed MIR codegen

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

- Canonical SPipe generation for source `84fc466174338171ab4bbbdb34e2070f1b06e06876361f8f4a1afeee6ea1a0dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84fc466174338171ab4bbbdb34e2070f1b06e06876361f8f4a1afeee6ea1a0dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84fc466174338171ab4bbbdb34e2070f1b06e06876361f8f4a1afeee6ea1a0dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/storage_simd_codegen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_codegen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/storage_simd_codegen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits typed f32x8 load binop and store for a proven full block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never emits a vector operation for a scalar tail block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses arrays with no full block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
