# i64.to_u32 Interpreter Method Resolution Specification

> Regression test for the interpreter gap where calling `.to_u32()` (and sibling numeric conversion methods) on an i64 receiver inside the Rust bootstrap interpreter failed with `method 'to_u32' not found on type 'i64'`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i64.to_u32 Interpreter Method Resolution Specification

Regression test for the interpreter gap where calling `.to_u32()` (and sibling numeric conversion methods) on an i64 receiver inside the Rust bootstrap interpreter failed with `method 'to_u32' not found on type 'i64'`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-TO-U32 |
| Category | Interpreter |
| Difficulty | 1/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/int_to_u32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the interpreter gap where calling `.to_u32()` (and sibling
numeric conversion methods) on an i64 receiver inside the Rust bootstrap
interpreter failed with `method 'to_u32' not found on type 'i64'`.

The fix lives in `handle_int_methods` (src/compiler_rust/compiler/src/
interpreter_method/primitives.rs) and the nested-call dispatch mirror in
`interpreter_helpers/method_dispatch.rs`. Both paths now map `to_i8`, `to_i16`,
`to_i32`, `to_i64`, `to_u8`, `to_u16`, `to_u32`, `to_u64` on Int receivers
through `cast_int_to_numeric`, matching the `expr as <T>` cast semantics.

This spec exercises every conversion variant so any future regression in the
primitive method table is caught immediately.

## Scenarios

### i64 numeric conversion methods

#### resolves to_u32 on a plain int receiver

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves to_u32 on a plain int receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to_u32 on a plain int receiver")
val n: i64 = 255
expect(n.to_u32() == 255).to_be_true()
```

</details>

#### resolves to_u32 on an int field read through a struct

- resolves to_u32 on an int field read through a struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to_u32 on an int field read through a struct")
val s = IntHolder(v: 128)
expect(s.v.to_u32() == 128).to_be_true()
```

</details>

#### resolves to_u32 chained with bit shift (mirrors Color.to_u32 pattern)

- resolves to_u32 chained with bit shift (mirrors Color.to_u32 pattern)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to_u32 chained with bit shift (mirrors Color.to_u32 pattern)")
val r: i64 = 0x12
val g: i64 = 0x34
val b: i64 = 0x56
val a: i64 = 0xFF
val packed = (a.to_u32() << 24) | (r.to_u32() << 16) | (g.to_u32() << 8) | b.to_u32()
expect(packed == 0xFF123456).to_be_true()
```

</details>

#### resolves to_u8 / to_u16 / to_u64 siblings

- resolves to_u8 / to_u16 / to_u64 siblings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to_u8 / to_u16 / to_u64 siblings")
val n: i64 = 42
expect(n.to_u8() == 42).to_be_true()
expect(n.to_u16() == 42).to_be_true()
expect(n.to_u64() == 42).to_be_true()
```

</details>

#### resolves to_i8 / to_i16 / to_i32 / to_i64 siblings

- resolves to_i8 / to_i16 / to_i32 / to_i64 siblings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to_i8 / to_i16 / to_i32 / to_i64 siblings")
val n: i64 = 7
expect(n.to_i8() == 7).to_be_true()
expect(n.to_i16() == 7).to_be_true()
expect(n.to_i32() == 7).to_be_true()
expect(n.to_i64() == 7).to_be_true()
```

</details>

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

- Canonical SPipe generation for source `f711374e0b0fa213b9e40c6073e7a846c72d2575237399bbdc670fa170962001`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f711374e0b0fa213b9e40c6073e7a846c72d2575237399bbdc670fa170962001`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f711374e0b0fa213b9e40c6073e7a846c72d2575237399bbdc670fa170962001`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/int_to_u32_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/int_to_u32_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/int_to_u32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/int_to_u32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/int_to_u32_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves to_u32 on a plain int receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/int_to_u32_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves to_u32 on an int field read through a struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/int_to_u32_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves to_u32 chained with bit shift (mirrors Color.to_u32 pattern)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
