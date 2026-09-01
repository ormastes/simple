# Cuda Ptx Mir Kind Primitive Class Specification

> Tests covering CUDA PTX MirTypeKind to PrimitiveType conversion class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Ptx Mir Kind Primitive Class Specification

## Scenarios

### CUDA PTX MirTypeKind to PrimitiveType conversion class

#### positive control: the mapper is loaded and distinguishes at least two kinds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: the mapper is loaded and distinguishes at least two kinds
   - Expected: u8_suffix equals `.u8`
   - Expected: f64_suffix equals `.f64`
   - Expected: u8_suffix == f64_suffix is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive control: the mapper is loaded and distinguishes at least two kinds")
val tm = cuda_type_mapper_create_sm(8, 6)
val u8_suffix = tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U8))
val f64_suffix = tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.F64))
expect(u8_suffix).to_equal(".u8")
expect(f64_suffix).to_equal(".f64")
expect(u8_suffix == f64_suffix).to_equal(false)
```

</details>

#### covers every signed and unsigned integer MIR scalar kind

- covers every signed and unsigned integer MIR scalar kind
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I8)) equals `.s8`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I16)) equals `.s16`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I32)) equals `.s32`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I64)) equals `.s64`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U8)) equals `.u8`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U16)) equals `.u16`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U32)) equals `.u32`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U64)) equals `.u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers every signed and unsigned integer MIR scalar kind")
val tm = cuda_type_mapper_create_sm(8, 6)
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I8))).to_equal(".s8")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I16))).to_equal(".s16")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I32))).to_equal(".s32")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.I64))).to_equal(".s64")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U8))).to_equal(".u8")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U16))).to_equal(".u16")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U32))).to_equal(".u32")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.U64))).to_equal(".u64")
```

</details>

#### covers float, bool and unit MIR scalar kinds

- covers float, bool and unit MIR scalar kinds
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.F32)) equals `.f32`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.F64)) equals `.f64`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Bool)) equals `.pred`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Unit)) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers float, bool and unit MIR scalar kinds")
val tm = cuda_type_mapper_create_sm(8, 6)
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.F32))).to_equal(".f32")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.F64))).to_equal(".f64")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Bool))).to_equal(".pred")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Unit))).to_equal("")
```

</details>

#### covers pointer-shaped kinds, which PTX addresses as 64-bit

- covers pointer-shaped kinds, which PTX addresses as 64-bit
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Ptr(MirType(kind: MirTypeKind.F32), true))) equals `.u64`
   - Expected: tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Ref(MirType(kind: MirTypeKind.I32), true))) equals `.u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers pointer-shaped kinds, which PTX addresses as 64-bit")
val tm = cuda_type_mapper_create_sm(8, 6)
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Ptr(MirType(kind: MirTypeKind.F32), true)))).to_equal(".u64")
expect(tm.ptx_type(ptx_mir_kind_to_primitive(MirTypeKind.Ref(MirType(kind: MirTypeKind.I32), true)))).to_equal(".u64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA PTX MirTypeKind to PrimitiveType conversion class.
- CUDA PTX MirTypeKind to PrimitiveType conversion class

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

- Canonical SPipe generation for source `a5147a4eca27a58637133a2335cbe6eef8da4fcd51b3b0dfc31bdbe2aadbeaf0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5147a4eca27a58637133a2335cbe6eef8da4fcd51b3b0dfc31bdbe2aadbeaf0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5147a4eca27a58637133a2335cbe6eef8da4fcd51b3b0dfc31bdbe2aadbeaf0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: the mapper is loaded and distinguishes at least two kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every signed and unsigned integer MIR scalar kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/cuda_ptx_mir_kind_primitive_class_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers float, bool and unit MIR scalar kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
