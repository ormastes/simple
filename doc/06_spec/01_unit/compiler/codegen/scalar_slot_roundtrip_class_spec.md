# Scalar Slot Roundtrip Class Specification

> Tests covering scalar slot round-trip across every erased-slot boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scalar Slot Roundtrip Class Specification

## Scenarios

### scalar slot round-trip across every erased-slot boundary

#### round-trips every primitive type through the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips every primitive type through the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm: it was correct in both bugs, so a red here means the probe is broken rather than the engine
- The probe must actually have executed its checks, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every primitive type through the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm: it was correct in both bugs, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("SCALAR_SLOT_ROUNDTRIP PROBE: ALL PASS")

step("The probe must actually have executed its checks, not exited early")
expect(interp).to_contain("PASS opt_i64_local")
expect(interp).to_contain("PASS field_f32_init")
expect(interp).to_contain("PASS array_i64_elem")
```

</details>

#### round-trips every primitive type through the cranelift JIT

- round-trips every primitive type through the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine both bugs lived in
- Nullable `T?` slots must carry i8/i16/i32/i64/u8/u16/u32/u64/f32/f64/bool/text payloads
- Struct fields must round-trip on both the construction and the assignment path
- Array elements, including a struct read out of an array
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every primitive type through the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine both bugs lived in")
val jit = run_probe_in_mode("jit")

step("Nullable `T?` slots must carry i8/i16/i32/i64/u8/u16/u32/u64/f32/f64/bool/text payloads")
expect(jit).to_contain("PASS opt_i64_local")
expect(jit).to_contain("PASS opt_u64_local")
expect(jit).to_contain("PASS opt_f64_local")
expect(jit).to_contain("PASS opt_bool_local")
expect(jit).to_contain("PASS opt_i64_coalesce")
expect(jit).to_contain("PASS opt_i64_return")

step("Struct fields must round-trip on both the construction and the assignment path")
expect(jit).to_contain("PASS field_f32_init")
expect(jit).to_contain("PASS field_f32_set")
expect(jit).to_contain("PASS field_i32_init")
expect(jit).to_contain("PASS field_u64_set")

step("Array elements, including a struct read out of an array")
expect(jit).to_contain("PASS array_f64_elem")
expect(jit).to_contain("PASS array_struct_f32_field")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("SCALAR_SLOT_ROUNDTRIP PROBE: ALL PASS")
```

</details>

#### shows no reinterpretation signature under either engine

- shows no reinterpretation signature under either engine
- Collect both engines' output
- A payload read through the wrong tag renders as a sub-normal double
   - Expected: jit does not contain `0.0000000000000000000`
   - Expected: interp does not contain `0.0000000000000000000`
- A never-unboxed tagged word leaks as `<value:0x..>`
   - Expected: jit does not contain `<value:0x`
   - Expected: interp does not contain `<value:0x`
- No check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no reinterpretation signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A payload read through the wrong tag renders as a sub-normal double")
expect(jit.contains("0.0000000000000000000")).to_equal(false)
expect(interp.contains("0.0000000000000000000")).to_equal(false)

step("A never-unboxed tagged word leaks as `<value:0x..>`")
expect(jit.contains("<value:0x")).to_equal(false)
expect(interp.contains("<value:0x")).to_equal(false)

step("No check may have failed under either engine")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scalar slot round-trip across every erased-slot boundary.
- scalar slot round-trip across every erased-slot boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19451a6b18935f472d2c7430b77578a768b44dcee3cdffa3afe3ac080ecc3417`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19451a6b18935f472d2c7430b77578a768b44dcee3cdffa3afe3ac080ecc3417`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19451a6b18935f472d2c7430b77578a768b44dcee3cdffa3afe3ac080ecc3417`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every primitive type through the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every primitive type through the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows no reinterpretation signature under either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
