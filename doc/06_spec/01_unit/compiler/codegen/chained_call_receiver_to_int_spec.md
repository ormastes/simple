# Chained Call Receiver To Int Specification

> Tests covering chained substring().to_int() under the JIT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Call Receiver To Int Specification

## Scenarios

### chained substring().to_int() under the JIT

#### gives 1234 in the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives 1234 in the interpreter (control arm)
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was always correct; a red here means the probe is broken, not the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives 1234 in the interpreter (control arm)")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was always correct; a red here means the probe is broken, not the engine")
expect(interp).to_contain("PASS substring_to_int_chained")
expect(interp).to_contain("PASS substring_to_int_stepped")
```

</details>

#### gives 1234 in the JIT for the CHAINED form, not a heap pointer

- gives 1234 in the JIT for the CHAINED form, not a heap pointer
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lived in
- The filed row: `"ab1234".substring(2).to_int()` must be 1234
- The bound-intermediate sibling was already correct and must stay correct
- No check may have failed, and the aggregate verdict is authoritative


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives 1234 in the JIT for the CHAINED form, not a heap pointer")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lived in")
val jit = run_probe_in_mode("jit")

step("The filed row: `\"ab1234\".substring(2).to_int()` must be 1234")
expect(jit).to_contain("PASS substring_to_int_chained")

step("The bound-intermediate sibling was already correct and must stay correct")
expect(jit).to_contain("PASS substring_to_int_stepped")

step("No check may have failed, and the aggregate verdict is authoritative")
expect_not(jit.contains("FAIL "))
expect(jit).to_contain("CHAINED_CALL_RECEIVER PROBE: ALL PASS")
```

</details>

#### does not return a pointer-shaped integer from a to_int on either engine

- does not return a pointer-shaped integer from a to_int on either engine
- Collect both engines' output
- The defect's signature is a 13-digit pointer where a 4-digit number belongs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not return a pointer-shaped integer from a to_int on either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("The defect's signature is a 13-digit pointer where a 4-digit number belongs")
expect_not(jit.contains("actual=25"))
expect_not(jit.contains("expected=1234 actual=1234"))
expect(interp).to_contain("CHAINED_CALL_RECEIVER PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering chained substring().to_int() under the JIT.
- chained substring().to_int() under the JIT

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

- Canonical SPipe generation for source `c2125c503da6c2f960a5d96d1ee6ba6683eb1d0f3e9b1366a7139573a7cff339`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2125c503da6c2f960a5d96d1ee6ba6683eb1d0f3e9b1366a7139573a7cff339`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2125c503da6c2f960a5d96d1ee6ba6683eb1d0f3e9b1366a7139573a7cff339`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives 1234 in the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives 1234 in the JIT for the CHAINED form, not a heap pointer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_call_receiver_to_int_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not return a pointer-shaped integer from a to_int on either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
