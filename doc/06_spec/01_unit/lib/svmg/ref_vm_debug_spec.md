# Ref Vm Debug Specification

> Tests covering DBG-1 inertness — DBG_FLAGS == 0 behaves exactly as before, DBG-1 debug conformance vectors on ref_vm, PROF-1 step counting, DBG-1 saved-state fidelity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ref Vm Debug Specification

## Scenarios

### DBG-1 inertness — DBG_FLAGS == 0 behaves exactly as before

#### a normal run reports no debug break and a zero step count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a normal run reports no debug break and a zero step count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a normal run reports no debug break and a zero step count")
val r = assemble_and_run(svmg_asm("PUSHI 1\nPUSHI 5\nSYS_RESULT\nHALT 0"), 1000, 0)
assert_equal(r.debug_break, false)
assert_equal(r.step_count, 0)
assert_equal(r.sentinel, SENTINEL_EXIT_MASK | 0)
```

</details>

#### a normal run leaves the DBG-1 block completely untouched

- a normal run leaves the DBG-1 block completely untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a normal run leaves the DBG-1 block completely untouched")
val r = assemble_and_run(svmg_asm("PUSHI 1\nPUSHI 5\nSYS_RESULT\nHALT 0"), 1000, 0)
assert_equal(dbg_read_flags(r.arena), 0)
assert_equal(dbg_read_saved_pc(r.arena), 0)
assert_equal(dbg_read_saved_sp(r.arena), 0)
assert_equal(dbg_read_saved_csp(r.arena), 0)
assert_equal(dbg_read_step_count(r.arena), 0)
```

</details>

#### a timeout with debugging off still writes only the timeout sentinel

- a timeout with debugging off still writes only the timeout sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a timeout with debugging off still writes only the timeout sentinel")
val r = assemble_and_run(svmg_asm("NOP\nJMP -4"), 5, 0)
assert_equal(r.timed_out, true)
assert_equal(r.debug_break, false)
assert_equal(dbg_read_step_count(r.arena), 0)
```

</details>

### DBG-1 debug conformance vectors on ref_vm

#### break-at-pc stops before the breakpoint instruction and resumes to completion

- break-at-pc stops before the breakpoint instruction and resumes to completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("break-at-pc stops before the breakpoint instruction and resumes to completion")
_check("break_at_pc")
```

</details>

#### single-step advances exactly one instruction per launch

- single-step advances exactly one instruction per launch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single-step advances exactly one instruction per launch")
_check("step_n")
```

</details>

#### clearing the breakpoint table lets a resume run to completion

- clearing the breakpoint table lets a resume run to completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clearing the breakpoint table lets a resume run to completion")
_check("resume_to_completion_after_clearing_breakpoints")
```

</details>

<details>
<summary>Advanced: a breakpoint inside a loop fires once per iteration with distinct state</summary>

#### a breakpoint inside a loop fires once per iteration with distinct state

- a breakpoint inside a loop fires once per iteration with distinct state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a breakpoint inside a loop fires once per iteration with distinct state")
_check("break_inside_loop")
```

</details>


</details>

#### a resumed launch sees the log and records written before the break

- a resumed launch sees the log and records written before the break


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a resumed launch sees the log and records written before the break")
_check("resume_with_persisted_arena")
```

</details>

#### a break inside a subroutine preserves the call stack across the launch

- a break inside a subroutine preserves the call stack across the launch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a break inside a subroutine preserves the call stack across the launch")
_check("break_in_subroutine_preserves_call_stack")
```

</details>

#### the step budget still expires while debugging, and state is still saved

- the step budget still expires while debugging, and state is still saved


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the step budget still expires while debugging, and state is still saved")
_check("budget_expiry_while_debugging")
```

</details>

#### a full breakpoint table honours its last entry

- a full breakpoint table honours its last entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a full breakpoint table honours its last entry")
_check("breakpoint_table_full")
```

</details>

### PROF-1 step counting

#### DBG_STEP_COUNT equals the exact instruction count of a straight-line program

- DBG_STEP_COUNT equals the exact instruction count of a straight-line program


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DBG_STEP_COUNT equals the exact instruction count of a straight-line program")
_check("step_count_accuracy_straightline")
```

</details>

<details>
<summary>Advanced: DBG_STEP_COUNT equals the exact instruction count of a looping program</summary>

#### DBG_STEP_COUNT equals the exact instruction count of a looping program

- DBG_STEP_COUNT equals the exact instruction count of a looping program


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DBG_STEP_COUNT equals the exact instruction count of a looping program")
_check("step_count_accuracy_loop")
```

</details>


</details>

#### DBG_STEP_COUNT accumulates across resumes rather than resetting per launch

- DBG_STEP_COUNT accumulates across resumes rather than resetting per launch


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DBG_STEP_COUNT accumulates across resumes rather than resetting per launch")
# The distinction PROF-1 exists for: `steps_used` is per-launch,
# DBG_STEP_COUNT is per-program. Asserted directly here so the
# difference is not merely implied by the vector table.
val v = _find("break_at_pc")
val code = svmg_asm(v.source)
var arena = build_arena(code, [], v.step_budget, v.entry_pc, DEFAULT_LOG_CAP)
arena = dbg_set_breakpoints(arena, [10])
arena = dbg_set_flags(arena, DBG_FLAG_ENABLED)
val first = run_arena(code, arena)
assert_equal(first.step_count, 2)
assert_equal(first.steps_used, 2)

arena = dbg_set_flags(first.arena, DBG_FLAG_ENABLED | DBG_FLAG_RESUME)
val second = run_arena(code, arena)
# 5 instructions ran in the second launch...
assert_equal(second.steps_used, 5)
# ...but the program has executed 7 in total.
assert_equal(second.step_count, 7)
```

</details>

### DBG-1 saved-state fidelity

#### saves negative operand-stack values as signed i32, not as a huge unsigned

- saves negative operand-stack values as signed i32, not as a huge unsigned


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saves negative operand-stack values as signed i32, not as a huge unsigned")
val code = svmg_asm("PUSHI -7\nPUSHI 3\nADD\nHALT 0")
var arena = build_arena(code, [], 1000, 0, DEFAULT_LOG_CAP)
arena = dbg_set_flags(arena, DBG_FLAG_ENABLED | DBG_FLAG_SINGLE_STEP)
val r = run_arena(code, arena)
assert_equal(r.debug_break, true)
assert_equal(r.sentinel, SENTINEL_DEBUG_BREAK)
assert_equal(dbg_read_saved_sp(r.arena), 1)
assert_equal(dbg_read_saved_stack_slot(r.arena, 0), -7)
```

</details>

#### restores a negative operand-stack value correctly on resume

- restores a negative operand-stack value correctly on resume


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores a negative operand-stack value correctly on resume")
val code = svmg_asm("PUSHI -7\nPUSHI 3\nADD\nPUSHI 1\nSWAP\nSYS_RESULT\nHALT 0")
var arena = build_arena(code, [], 1000, 0, DEFAULT_LOG_CAP)
arena = dbg_set_breakpoints(arena, [5])
arena = dbg_set_flags(arena, DBG_FLAG_ENABLED)
val first = run_arena(code, arena)
assert_equal(first.debug_break, true)
assert_equal(dbg_read_saved_stack_slot(first.arena, 0), -7)

arena = dbg_set_flags(first.arena, DBG_FLAG_ENABLED | DBG_FLAG_RESUME)
val second = run_arena(code, arena)
assert_equal(second.debug_break, false)
assert_equal(second.record_count, 1)
# -7 + 3 = -4, which only comes out right if the restore sign-extended.
assert_equal(read_records(second.arena, second.log_cap, 1)[0].value, -4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/svmg/ref_vm_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DBG-1 inertness — DBG_FLAGS == 0 behaves exactly as before, DBG-1 debug conformance vectors on ref_vm, PROF-1 step counting, DBG-1 saved-state fidelity.
- DBG-1 inertness — DBG_FLAGS == 0 behaves exactly as before
- DBG-1 debug conformance vectors on ref_vm
- PROF-1 step counting
- DBG-1 saved-state fidelity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `6717143dc1252d569465a70149163b79137909d8aec3b271266f292646f08df8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6717143dc1252d569465a70149163b79137909d8aec3b271266f292646f08df8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6717143dc1252d569465a70149163b79137909d8aec3b271266f292646f08df8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/svmg/ref_vm_debug_spec.spl
mirror: doc/06_spec/01_unit/lib/svmg/ref_vm_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/svmg/ref_vm_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/svmg/ref_vm_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/svmg/ref_vm_debug_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a normal run reports no debug break and a zero step count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/ref_vm_debug_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a normal run leaves the DBG-1 block completely untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/svmg/ref_vm_debug_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a timeout with debugging off still writes only the timeout sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
