# F32 Struct Field Roundtrip Specification

> Tests covering f32 struct field round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# F32 Struct Field Roundtrip Specification

## Scenarios

### f32 struct field round-trip

#### reads a constructor-initialised f32 field back as the value that was stored

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a constructor-initialised f32 field back as the value that was stored
- Construct a struct with an f32 field and an f64 field
- Read the f32 field back and compare against the absolute stored value
   - Expected: s.a == 2.5 is true
- The neighbouring f64 field was never affected and must stay correct
   - Expected: s.b == 3.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a constructor-initialised f32 field back as the value that was stored")
step("Construct a struct with an f32 field and an f64 field")
val s = F32Holder(a: 2.5, b: 3.5)

step("Read the f32 field back and compare against the absolute stored value")
expect(s.a == 2.5).to_equal(true)

step("The neighbouring f64 field was never affected and must stay correct")
expect(s.b == 3.5).to_equal(true)
```

</details>

#### reads an assigned f32 field back as the value that was assigned

- reads an assigned f32 field back as the value that was assigned
- Construct, then assign a new value through the field-set path
- The assignment path stores at the slot's declared width
   - Expected: t.a == 7.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads an assigned f32 field back as the value that was assigned")
step("Construct, then assign a new value through the field-set path")
var t = F32Holder(a: 0.0, b: 0.0)
t.a = 7.5

step("The assignment path stores at the slot's declared width")
expect(t.a == 7.5).to_equal(true)
```

</details>

#### reads a nested struct's f32 field back without truncation

- reads a nested struct's f32 field back without truncation
- Nest a struct carrying an f32 field one level down
- A nested read is the same field read one level down
   - Expected: o.inner.a == 1.25 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a nested struct's f32 field back without truncation")
step("Nest a struct carrying an f32 field one level down")
val o = F32Outer(inner: F32Holder(a: 1.25, b: 0.0))

step("A nested read is the same field read one level down")
expect(o.inner.a == 1.25).to_equal(true)
```

</details>

#### keeps a value whose f64 low half is non-zero from becoming a denormal

- keeps a value whose f64 low half is non-zero from becoming a denormal
- Store 0.1, whose f64 bit pattern has a non-zero low 32 bits
- Truncation would yield -1.588e-23; a real demote yields 0.1f32
   - Expected: s.a > 0.09 is true
   - Expected: s.a < 0.11 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a value whose f64 low half is non-zero from becoming a denormal")
step("Store 0.1, whose f64 bit pattern has a non-zero low 32 bits")
val s = F32Holder(a: 0.1, b: 0.0)

step("Truncation would yield -1.588e-23; a real demote yields 0.1f32")
expect(s.a > 0.09).to_equal(true)
expect(s.a < 0.11).to_equal(true)
```

</details>

#### agrees between the interpreter and the cranelift JIT on every f32 field read

- agrees between the interpreter and the cranelift JIT on every f32 field read
- Write the bug report's minimal repro to a temporary source file
- Run it under SIMPLE_EXECUTION_MODE=interpreter — the engine that was always correct
- Run the same file under SIMPLE_EXECUTION_MODE=jit — the engine that was wrong
- Both engines must produce the same output, and it must be the correct one
- The truncation signature must appear in neither engine's output
   - Expected: jit does not contain `-0.0000000000000000000000158`
   - Expected: interp does not contain `-0.0000000000000000000000158`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between the interpreter and the cranelift JIT on every f32 field read")
step("Write the bug report's minimal repro to a temporary source file")
step("Run it under SIMPLE_EXECUTION_MODE=interpreter — the engine that was always correct")
val interp = run_repro_in_mode("interpreter")

step("Run the same file under SIMPLE_EXECUTION_MODE=jit — the engine that was wrong")
val jit = run_repro_in_mode("jit")

step("Both engines must produce the same output, and it must be the correct one")
expect(interp).to_contain("2.5")
expect(interp).to_contain("3.5")
expect(interp).to_contain("7.5")
expect(interp).to_contain("1.25")
expect(jit).to_contain("2.5")
expect(jit).to_contain("3.5")
expect(jit).to_contain("7.5")
expect(jit).to_contain("1.25")

step("The truncation signature must appear in neither engine's output")
expect(jit.contains("-0.0000000000000000000000158")).to_equal(false)
expect(interp.contains("-0.0000000000000000000000158")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering f32 struct field round-trip.
- f32 struct field round-trip

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd263bb332cad4e9b6cfc0034ac125b3cb64cdc318dab2f208e777e2cbb08628`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd263bb332cad4e9b6cfc0034ac125b3cb64cdc318dab2f208e777e2cbb08628`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd263bb332cad4e9b6cfc0034ac125b3cb64cdc318dab2f208e777e2cbb08628`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a constructor-initialised f32 field back as the value that was stored' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads an assigned f32 field back as the value that was assigned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a nested struct's f32 field back without truncation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
