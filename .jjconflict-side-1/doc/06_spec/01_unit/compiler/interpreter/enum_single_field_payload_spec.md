# Enum Single Field Payload Specification

> Tests covering enum payload extraction is arity- and type-independent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Single Field Payload Specification

## Scenarios

### enum payload extraction is arity- and type-independent

#### extracts single-field payloads unshifted under the run path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts single-field payloads unshifted under the run path
- Run the run-path probe under the default engine used by `bin/simple run`
- The report's own values: a `>> 3` corruption turns these into 8, 12, 31 and 0
- Tag-boundary neighbours, where a shift defect is easiest to miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts single-field payloads unshifted under the run path")
step("Run the run-path probe under the default engine used by `bin/simple run`")
val jit = run_probe_in_mode("jit")

step("The report's own values: a `>> 3` corruption turns these into 8, 12, 31 and 0")
expect(jit).to_contain("PASS one_65")
expect(jit).to_contain("PASS one_100")
expect(jit).to_contain("PASS one_255")
expect(jit).to_contain("PASS one_1")

step("Tag-boundary neighbours, where a shift defect is easiest to miss")
expect(jit).to_contain("PASS one_7")
expect(jit).to_contain("PASS one_8")
expect(jit).to_contain("PASS one_neg")
expect(jit).to_contain("PASS one_big")
```

</details>

#### extracts multi-field payloads, the report's stated control arm

- extracts multi-field payloads, the report's stated control arm
- Two- and three-field variants must remain correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts multi-field payloads, the report's stated control arm")
step("Two- and three-field variants must remain correct")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS two_x")
expect(jit).to_contain("PASS two_y")
expect(jit).to_contain("PASS three_a")
expect(jit).to_contain("PASS three_c")
```

</details>

#### extracts single-field payloads of non-integer type

- extracts single-field payloads of non-integer type
- A boxed-integer tag defect can only touch integers, so text and bool generalise the class


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts single-field payloads of non-integer type")
step("A boxed-integer tag defect can only touch integers, so text and bool generalise the class")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("PASS str_payload")
expect(jit).to_contain("PASS flag_payload")
```

</details>

#### agrees with the interpreter, and neither engine reports a failure

- agrees with the interpreter, and neither engine reports a failure
- The interpreter is the control engine the report says was correct
- The run path must reach the same aggregate verdict
- No individual check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the interpreter, and neither engine reports a failure")
step("The interpreter is the control engine the report says was correct")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("ENUM_PAYLOAD PROBE: ALL PASS")

step("The run path must reach the same aggregate verdict")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("ENUM_PAYLOAD PROBE: ALL PASS")

step("No individual check may have failed under either engine")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum payload extraction is arity- and type-independent.
- enum payload extraction is arity- and type-independent

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `478ecb58db3fe2fcfda4a4deb9ef40218f734af3dbc949f5d8f6310921becb01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `478ecb58db3fe2fcfda4a4deb9ef40218f734af3dbc949f5d8f6310921becb01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `478ecb58db3fe2fcfda4a4deb9ef40218f734af3dbc949f5d8f6310921becb01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/enum_single_field_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/enum_single_field_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/enum_single_field_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts single-field payloads unshifted under the run path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts multi-field payloads, the report's stated control arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts single-field payloads of non-integer type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
