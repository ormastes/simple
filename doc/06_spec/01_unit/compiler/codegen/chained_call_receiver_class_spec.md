# Chained Call Receiver Class Specification

> Tests covering a call result used as a receiver, across every producer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Call Receiver Class Specification

## Scenarios

### a call result used as a receiver, across every producer

#### resolves every chained-receiver form in the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves every chained-receiver form in the interpreter (control arm)
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter carries real values, not typed vregs, so it is the control


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves every chained-receiver form in the interpreter (control arm)")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter carries real values, not typed vregs, so it is the control")
expect(interp).to_contain("CHAINED_CALL_RECEIVER PROBE: ALL PASS")
expect_not(interp.contains("FAIL "))
```

</details>

#### types every STRING-producing call result under the JIT

- types every STRING-producing call result under the JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit
- substring() as a producer, into each numeric and text consumer
- The other string producers that lower to the same MirInst::Call shape
- Nesting: a chained result feeding another chained call


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("types every STRING-producing call result under the JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("substring() as a producer, into each numeric and text consumer")
expect(jit).to_contain("PASS substring_to_int_chained")
expect(jit).to_contain("PASS substring_to_i64_chained")
expect(jit).to_contain("PASS substring_to_float_chained")
expect(jit).to_contain("PASS substring_to_upper_chained")
expect(jit).to_contain("PASS substring_len_chained")

step("The other string producers that lower to the same MirInst::Call shape")
expect(jit).to_contain("PASS slice_to_int_chained")
expect(jit).to_contain("PASS trim_to_int_chained")
expect(jit).to_contain("PASS to_upper_to_lower_chained")
expect(jit).to_contain("PASS concat_to_int_chained")

step("Nesting: a chained result feeding another chained call")
expect(jit).to_contain("PASS substring_substring_chained")
```

</details>

#### leaves ARRAY receivers of the shared runtime symbols alone

- leaves ARRAY receivers of the shared runtime symbols alone
- Run the probe under the JIT
- rt_slice/rt_take/rt_reverse serve BOTH String and Array receivers; typing their result String unconditionally would corrupt these


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves ARRAY receivers of the shared runtime symbols alone")
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("rt_slice/rt_take/rt_reverse serve BOTH String and Array receivers; typing their result String unconditionally would corrupt these")
expect(jit).to_contain("PASS array_slice_len_chained")
expect(jit).to_contain("PASS array_slice_index_chained")
```

</details>

#### shows no pointer-as-integer signature under either engine

- shows no pointer-as-integer signature under either engine
- Collect both engines' output
- A never-decoded heap word leaks as `<value:0x..>` or an invalid-heap render
- No check may have failed under either engine
- Both aggregate verdicts must be green


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no pointer-as-integer signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A never-decoded heap word leaks as `<value:0x..>` or an invalid-heap render")
expect_not(jit.contains("<value:0x"))
expect_not(jit.contains("<invalid-heap:"))
expect_not(interp.contains("<value:0x"))

step("No check may have failed under either engine")
expect_not(jit.contains("FAIL "))
expect_not(interp.contains("FAIL "))

step("Both aggregate verdicts must be green")
expect(jit).to_contain("CHAINED_CALL_RECEIVER PROBE: ALL PASS")
expect(interp).to_contain("CHAINED_CALL_RECEIVER PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/chained_call_receiver_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering a call result used as a receiver, across every producer.
- a call result used as a receiver, across every producer

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

- Canonical SPipe generation for source `8bdb46e069db6faa8f86f430dcd042c9d9d6f611a70c3a2f1d8b3be841fad01b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8bdb46e069db6faa8f86f430dcd042c9d9d6f611a70c3a2f1d8b3be841fad01b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8bdb46e069db6faa8f86f430dcd042c9d9d6f611a70c3a2f1d8b3be841fad01b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/chained_call_receiver_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/chained_call_receiver_class_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every chained-receiver form in the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_call_receiver_class_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'types every STRING-producing call result under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_call_receiver_class_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves ARRAY receivers of the shared runtime symbols alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
