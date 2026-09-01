# I8 Int Boxing Repro Specification

> Tests covering i8 is boxed as an integer, not as a bool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I8 Int Boxing Repro Specification

## Scenarios

### i8 is boxed as an integer, not as a bool

#### runs the probe to completion under the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the probe to completion under the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The probe must have reached its end — a truncated run is not evidence
- The interpreter was correct in this bug, so a red here means the probe is broken, not the engine
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the probe to completion under the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The probe must have reached its end — a truncated run is not evidence")
expect(interp).to_contain("I8_INT_BOXING PROBE: DONE")

step("The interpreter was correct in this bug, so a red here means the probe is broken, not the engine")
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

#### reads back every i8 as the value that was written, under the JIT

- reads back every i8 as the value that was written, under the JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- The probe must have reached its end
- An i8 array literal read back in the same function
- The same array returned across a call boundary
- The literal numeric signature: 5 must never read back as 43
   - Expected: jit does not contain `actual=43`
- The fix routes i8 to the integer tag; bool must still reach rt_value_bool
- No check may have failed — this is the authoritative verdict
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads back every i8 as the value that was written, under the JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("The probe must have reached its end")
expect(jit).to_contain("I8_INT_BOXING PROBE: DONE")

step("An i8 array literal read back in the same function")
expect(jit).to_contain("PASS arr_i8_elem0")
expect(jit).to_contain("PASS arr_i8_elem1")
expect(jit).to_contain("PASS arr_i8_elem2")

step("The same array returned across a call boundary")
expect(jit).to_contain("PASS ret_i8_elem0")
expect(jit).to_contain("PASS ret_i8_elem2")

step("The literal numeric signature: 5 must never read back as 43")
expect(jit).to_contain("PASS arr_i8_tag_special_signature")
expect(jit.contains("actual=43")).to_equal(false)

step("The fix routes i8 to the integer tag; bool must still reach rt_value_bool")
expect(jit).to_contain("PASS bool_true_unaffected")
expect(jit).to_contain("PASS bool_false_unaffected")

step("No check may have failed — this is the authoritative verdict")
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/i8_int_boxing_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i8 is boxed as an integer, not as a bool.
- i8 is boxed as an integer, not as a bool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `d8a00cf2bdf0f55a2798e4e6f31dc948443fd8474d927ae6043d26dc158c6ef9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8a00cf2bdf0f55a2798e4e6f31dc948443fd8474d927ae6043d26dc158c6ef9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8a00cf2bdf0f55a2798e4e6f31dc948443fd8474d927ae6043d26dc158c6ef9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/i8_int_boxing_repro_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/i8_int_boxing_repro_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/i8_int_boxing_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/i8_int_boxing_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/i8_int_boxing_repro_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the probe to completion under the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/i8_int_boxing_repro_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads back every i8 as the value that was written, under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
