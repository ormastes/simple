# Struct Field Width Roundtrip Specification

> Tests covering struct field store and load widths agree.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Field Width Roundtrip Specification

## Scenarios

### struct field store and load widths agree

#### round-trips every declared field width through the constructor path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips every declared field width through the constructor path
- Construct one struct carrying a 4-byte float, an 8-byte float, and two narrow integers
- Each field must read back the literal that was stored, not a re-widened neighbour
   - Expected: w.f == 2.5 is true
   - Expected: w.d == 3.5 is true
   - Expected: w.i == 1000 is true
   - Expected: w.b == 200 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every declared field width through the constructor path")
step("Construct one struct carrying a 4-byte float, an 8-byte float, and two narrow integers")
val w = Widths(f: 2.5, d: 3.5, i: 1000, b: 200)

step("Each field must read back the literal that was stored, not a re-widened neighbour")
expect(w.f == 2.5).to_equal(true)
expect(w.d == 3.5).to_equal(true)
expect(w.i == 1000).to_equal(true)
expect(w.b == 200).to_equal(true)
```

</details>

#### round-trips every declared field width through the assignment path

- round-trips every declared field width through the assignment path
- Start from a zeroed struct so a no-op store cannot masquerade as a pass
- Assign each field a value distinct from its initial value
- Every assigned field reads back exactly what was assigned
   - Expected: w.f == 0.25 is true
   - Expected: w.d == 1.75 is true
   - Expected: w.i == 77 is true
   - Expected: w.b == 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips every declared field width through the assignment path")
step("Start from a zeroed struct so a no-op store cannot masquerade as a pass")
var w = Widths(f: 0.0, d: 0.0, i: 0, b: 0)

step("Assign each field a value distinct from its initial value")
w.f = 0.25
w.d = 1.75
w.i = 77
w.b = 5

step("Every assigned field reads back exactly what was assigned")
expect(w.f == 0.25).to_equal(true)
expect(w.d == 1.75).to_equal(true)
expect(w.i == 77).to_equal(true)
expect(w.b == 5).to_equal(true)
```

</details>

#### round-trips a narrow field of a struct held in an array element

- round-trips a narrow field of a struct held in an array element
- An array element read is the same field read one indirection down
   - Expected: arr[0].f == 1.5 is true
   - Expected: arr[0].d == 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips a narrow field of a struct held in an array element")
step("An array element read is the same field read one indirection down")
val arr = [Widths(f: 1.5, d: 0.0, i: 1, b: 1)]
expect(arr[0].f == 1.5).to_equal(true)
expect(arr[0].d == 0.0).to_equal(true)
```

</details>

#### keeps a narrow float field usable in arithmetic after the round-trip

- keeps a narrow float field usable in arithmetic after the round-trip
- A truncated field reads as 0.0 or a denormal, so arithmetic over it collapses
- Compare against the absolute expected sum, not against the field itself
   - Expected: doubled > 4.99 is true
   - Expected: doubled < 5.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a narrow float field usable in arithmetic after the round-trip")
step("A truncated field reads as 0.0 or a denormal, so arithmetic over it collapses")
val w = Widths(f: 2.5, d: 0.0, i: 0, b: 0)
val doubled = w.f + w.f

step("Compare against the absolute expected sum, not against the field itself")
expect(doubled > 4.99).to_equal(true)
expect(doubled < 5.01).to_equal(true)
```

</details>

#### produces identical field reads under the interpreter and the cranelift JIT

- produces identical field reads under the interpreter and the cranelift JIT
- Sweep every declared width through both store paths in a subprocess
- Every expected value appears in both engines' output
- Neither engine may emit the low-half truncation signature
   - Expected: jit does not contain `-0.00000000000000000000`
   - Expected: interp does not contain `-0.00000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces identical field reads under the interpreter and the cranelift JIT")
step("Sweep every declared width through both store paths in a subprocess")
val interp = run_width_sweep("interpreter")
val jit = run_width_sweep("jit")

step("Every expected value appears in both engines' output")
for line in EXPECTED_LINES:
    expect(interp).to_contain(line)
    expect(jit).to_contain(line)

step("Neither engine may emit the low-half truncation signature")
expect(jit.contains("-0.00000000000000000000")).to_equal(false)
expect(interp.contains("-0.00000000000000000000")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering struct field store and load widths agree.
- struct field store and load widths agree

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

- Canonical SPipe generation for source `2375d4b619d200a03f4beff4b99221217f455c5ee216d52166acd6c4a4779fd2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2375d4b619d200a03f4beff4b99221217f455c5ee216d52166acd6c4a4779fd2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2375d4b619d200a03f4beff4b99221217f455c5ee216d52166acd6c4a4779fd2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every declared field width through the constructor path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every declared field width through the assignment path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a narrow field of a struct held in an array element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
