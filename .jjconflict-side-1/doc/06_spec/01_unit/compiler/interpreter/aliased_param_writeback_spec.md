# Aliased Param Writeback Specification

> Tests covering aliased parameter write-back does not discard the mutation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aliased Param Writeback Specification

## Scenarios

### aliased parameter write-back does not discard the mutation

#### keeps the mutation when the same binding is passed as mut and non-mut (interpreter)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the mutation when the same binding is passed as mut and non-mut (interpreter)
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter — the engine the defect lived in
- The filed shape: fn f(mut a, b) called as f(w, w) must push into the caller's array
- The mirror image: fn f(b, mut a). A first-write-wins fix would pass the shape above and fail here
- An immutable alias on BOTH sides of the mutable parameter
- Named-argument syntax reaches the same write-back path and must behave identically
- Dicts and class instances share the copy-on-write handle model, so they share the class
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the mutation when the same binding is passed as mut and non-mut (interpreter)")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter — the engine the defect lived in")
val interp = run_probe_in_mode("interpreter")

step("The filed shape: fn f(mut a, b) called as f(w, w) must push into the caller's array")
expect(interp).to_contain("PASS aliased_array_mut_first")
expect(interp).to_contain("PASS aliased_array_mut_first_value")

step("The mirror image: fn f(b, mut a). A first-write-wins fix would pass the shape above and fail here")
expect(interp).to_contain("PASS aliased_array_mut_second")

step("An immutable alias on BOTH sides of the mutable parameter")
expect(interp).to_contain("PASS aliased_array_mut_middle")

step("Named-argument syntax reaches the same write-back path and must behave identically")
expect(interp).to_contain("PASS aliased_array_named_args")

step("Dicts and class instances share the copy-on-write handle model, so they share the class")
expect(interp).to_contain("PASS aliased_dict_mut_first")
expect(interp).to_contain("PASS aliased_dict_mut_second")
expect(interp).to_contain("PASS aliased_object_mut_second")

step("The aggregate verdict line is the authoritative result")
expect(interp).to_contain("ALIASED_PARAM_WRITEBACK PROBE: ALL PASS")
```

</details>

#### does not regress the non-aliased write-back it is scoped around (interpreter)

- does not regress the non-aliased write-back it is scoped around (interpreter)
- The fix must be invisible when each caller binding reaches exactly one parameter
- A mut parameter with a distinct argument still writes back
- An immutable parameter with a distinct argument still must NOT write back
- When NO alias is declared mut, nothing may reach the caller — the callee body must still have run


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not regress the non-aliased write-back it is scoped around (interpreter)")
step("The fix must be invisible when each caller binding reaches exactly one parameter")
val interp = run_probe_in_mode("interpreter")

step("A mut parameter with a distinct argument still writes back")
expect(interp).to_contain("PASS control_non_aliased_writeback")
expect(interp).to_contain("PASS control_distinct_bindings_mut")

step("An immutable parameter with a distinct argument still must NOT write back")
expect(interp).to_contain("PASS control_distinct_bindings_immut")

step("When NO alias is declared mut, nothing may reach the caller — the callee body must still have run")
expect(interp).to_contain("PASS neither_mut_ran")
expect(interp).to_contain("PASS aliased_array_neither_mut")
```

</details>

#### agrees with the cranelift JIT, which was already correct

- agrees with the cranelift JIT, which was already correct
- Run the identical probe under SIMPLE_EXECUTION_MODE=jit
- The JIT arm is the proof that every expectation above is achievable, not invented


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the cranelift JIT, which was already correct")
step("Run the identical probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("The JIT arm is the proof that every expectation above is achievable, not invented")
expect(jit).to_contain("ALIASED_PARAM_WRITEBACK PROBE: ALL PASS")
```

</details>

#### pins the known-open both-aliases-mut residual so it cannot move unnoticed

- pins the known-open both-aliases-mut residual so it cannot move unnoticed
- When BOTH aliases are declared mut the interpreter still loses one push
- Recorded, not asserted as correct: each mut parameter forks its own Arc and the last write-back wins. Fixing it needs the two parameter bindings to share one handle.
- The JIT gets the right answer, so this remains a live engine divergence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pins the known-open both-aliases-mut residual so it cannot move unnoticed")
step("When BOTH aliases are declared mut the interpreter still loses one push")
val interp = run_probe_in_mode("interpreter")

step("Recorded, not asserted as correct: each mut parameter forks its own Arc and the last write-back wins. Fixing it needs the two parameter bindings to share one handle.")
expect(interp).to_contain("OBSERVE aliased_array_both_mut=2")

step("The JIT gets the right answer, so this remains a live engine divergence")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("OBSERVE aliased_array_both_mut=3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aliased parameter write-back does not discard the mutation.
- aliased parameter write-back does not discard the mutation

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

- Canonical SPipe generation for source `6eedb25aac4c6e8903f5db1cfd8e30239ff77c5189a47443ac2a1744f488a494`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6eedb25aac4c6e8903f5db1cfd8e30239ff77c5189a47443ac2a1744f488a494`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6eedb25aac4c6e8903f5db1cfd8e30239ff77c5189a47443ac2a1744f488a494`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/aliased_param_writeback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/aliased_param_writeback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/aliased_param_writeback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the mutation when the same binding is passed as mut and non-mut (interpreter)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not regress the non-aliased write-back it is scoped around (interpreter)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the cranelift JIT, which was already correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
