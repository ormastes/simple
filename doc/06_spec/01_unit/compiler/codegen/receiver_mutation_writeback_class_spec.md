# Receiver Mutation Writeback Class Specification

> Tests covering receiver and parameter mutations are written back on every engine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Receiver Mutation Writeback Class Specification

## Scenarios

### receiver and parameter mutations are written back on every engine

#### writes back every mutation shape on the tree-walk interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes back every mutation shape on the tree-walk interpreter
- Run the class probe under SIMPLE_EXECUTION_MODE=interpreter
- Non-vacuity: the probe must have executed its first case, not been demoted or exited early
- An explicit `mut` struct parameter must observe the callee's write — the interpreter's known gap
- A class receiver must be equivalent to a struct receiver here
- No shape in the sweep may fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes back every mutation shape on the tree-walk interpreter")
step("Run the class probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("Non-vacuity: the probe must have executed its first case, not been demoted or exited early")
expect(interp).to_contain("PASS struct_receiver")

step("An explicit `mut` struct parameter must observe the callee's write — the interpreter's known gap")
expect(interp).to_contain("PASS mut_parameter")

step("A class receiver must be equivalent to a struct receiver here")
expect(interp).to_contain("PASS class_receiver")

step("No shape in the sweep may fail")
expect(interp).to_contain("RECEIVER_WRITEBACK CLASS PROBE: ALL PASS")
```

</details>

#### writes back every mutation shape on the default JIT engine

- writes back every mutation shape on the default JIT engine
- Run the same class probe under SIMPLE_EXECUTION_MODE=jit
- Non-vacuity: a case the JIT already gets right must be present, proving the probe ran on this arm too
- A struct receiver must persist `self.n = self.n + 1` — the JIT's core gap
- Repeating the call in a loop must accumulate, not reset
- Three field hops to a struct receiver must behave like zero hops
- The direct-assignment spelling of the same place is the control: it must also stay correct
- No shape in the sweep may fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes back every mutation shape on the default JIT engine")
step("Run the same class probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("Non-vacuity: a case the JIT already gets right must be present, proving the probe ran on this arm too")
expect(jit).to_contain("PASS class_receiver")

step("A struct receiver must persist `self.n = self.n + 1` — the JIT's core gap")
expect(jit).to_contain("PASS struct_receiver")

step("Repeating the call in a loop must accumulate, not reset")
expect(jit).to_contain("PASS loop_three_calls")

step("Three field hops to a struct receiver must behave like zero hops")
expect(jit).to_contain("PASS depth3_method")

step("The direct-assignment spelling of the same place is the control: it must also stay correct")
expect(jit).to_contain("PASS depth3_assignment")

step("No shape in the sweep may fail")
expect(jit).to_contain("RECEIVER_WRITEBACK CLASS PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering receiver and parameter mutations are written back on every engine.
- receiver and parameter mutations are written back on every engine

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

- Canonical SPipe generation for source `88658081b71eb971fe25f62368df97d13c96121efd10ff4a6e0407bd758d345d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88658081b71eb971fe25f62368df97d13c96121efd10ff4a6e0407bd758d345d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88658081b71eb971fe25f62368df97d13c96121efd10ff4a6e0407bd758d345d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes back every mutation shape on the tree-walk interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/receiver_mutation_writeback_class_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes back every mutation shape on the default JIT engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
