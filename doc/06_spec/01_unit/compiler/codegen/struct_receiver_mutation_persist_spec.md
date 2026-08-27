# Struct Receiver Mutation Persist Specification

> Tests covering a mutating method call persists its write to the receiver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Receiver Mutation Persist Specification

## Scenarios

### a mutating method call persists its write to the receiver

#### persists the mutation on the tree-walk interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- persists the mutation on the tree-walk interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The probe must actually have executed, not exited early or been demoted
- Every receiver depth must round-trip on the control engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("persists the mutation on the tree-walk interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The probe must actually have executed, not exited early or been demoted")
expect(interp).to_contain("PASS depth0_bump_twice")

step("Every receiver depth must round-trip on the control engine")
expect(interp).to_contain("RECEIVER_MUTATION PROBE: ALL PASS")
```

</details>

#### persists the mutation on the default JIT engine

- persists the mutation on the default JIT engine
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine `bin/simple run` uses by default
- Depth 0: `l.bump()` on a plain local struct must leave n == 2 after two calls
- Depth 0 with an argument: `l.set_to(7)` must leave n == 7, proving the write and not merely the call survived
- Depth 1: one field hop to the receiver must behave identically
- Depth 2: the shape originally filed as selfhost_two_hop_field_method_mutation_lost_2026-07-27
- No failure line may appear at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("persists the mutation on the default JIT engine")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine `bin/simple run` uses by default")
val jit = run_probe_in_mode("jit")

step("Depth 0: `l.bump()` on a plain local struct must leave n == 2 after two calls")
expect(jit).to_contain("PASS depth0_bump_twice")

step("Depth 0 with an argument: `l.set_to(7)` must leave n == 7, proving the write and not merely the call survived")
expect(jit).to_contain("PASS depth0_set_to")

step("Depth 1: one field hop to the receiver must behave identically")
expect(jit).to_contain("PASS depth1_bump_twice")

step("Depth 2: the shape originally filed as selfhost_two_hop_field_method_mutation_lost_2026-07-27")
expect(jit).to_contain("PASS depth2_bump_twice")

step("No failure line may appear at all")
expect(jit).to_contain("RECEIVER_MUTATION PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering a mutating method call persists its write to the receiver.
- a mutating method call persists its write to the receiver

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

- Canonical SPipe generation for source `958056297cc85528679df4cb99d0a5b0631914f87ac76933b69f39bb8aa2c69c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `958056297cc85528679df4cb99d0a5b0631914f87ac76933b69f39bb8aa2c69c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `958056297cc85528679df4cb99d0a5b0631914f87ac76933b69f39bb8aa2c69c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists the mutation on the tree-walk interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/struct_receiver_mutation_persist_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists the mutation on the default JIT engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
