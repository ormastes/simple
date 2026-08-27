# x86_64 User Entry Validation Specification

> SimpleOS needs a final live QEMU proof for AP green-carrier ring/user handoff, but hosted tests must not execute the x86_64 `iretq` user-entry bridge. This spec covers the safe prerequisite: the scheduler can expose a user handoff TCB with a valid user context and CR3 value, and the syscall-14 validation layer can accept or reject that record before the architecture bridge runs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 User Entry Validation Specification

SimpleOS needs a final live QEMU proof for AP green-carrier ring/user handoff, but hosted tests must not execute the x86_64 `iretq` user-entry bridge. This spec covers the safe prerequisite: the scheduler can expose a user handoff TCB with a valid user context and CR3 value, and the syscall-14 validation layer can accept or reject that record before the architecture bridge runs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

SimpleOS needs a final live QEMU proof for AP green-carrier ring/user handoff,
but hosted tests must not execute the x86_64 `iretq` user-entry bridge. This
spec covers the safe prerequisite: the scheduler can expose a user handoff TCB
with a valid user context and CR3 value, and the syscall-14 validation layer can
accept or reject that record before the architecture bridge runs.

The positive scenario uses `Scheduler.create_user_task_pid`, so it exercises
the scheduler's real user-task construction path, including
`create_user_address_space` and `_map_user_process_image` when the hosted VMM is
available.

## Syntax

The validation API is:

```simple
validate_enter_user_blocking_handoff(pid_hint, scheduler)
```

It returns `ok=false` with an error string for missing or malformed handoff
state, and `ok=true` with the selected pid, context, and CR3 when the syscall
path is ready to call the architecture enter function.

## Evidence Boundary

Passing this spec does not satisfy `HW_HANDOFF_PASS=true`,
`USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`. Those markers remain
reserved for the opt-in live QEMU hardware/user gate.

**Requirements:** doc/02_requirements/feature/multicore_green.md
**Plan:** doc/03_plan/sys_test/multicore_green.md
**Design:** doc/05_design/multicore_green.md
**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### x86_64 user entry validation

#### rejects a missing user handoff task without entering ring-3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a missing user handoff task without entering ring-3
- validate an empty scheduler
   - Expected: validation.error equals `handoff task not found`
   - Expected: validation.pid equals `701u64`
   - Expected: validation.cr3 equals `0u64`
   - Expected: context_present equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a missing user handoff task without entering ring-3")
step("validate an empty scheduler")
val validation = validate_enter_user_blocking_handoff(701u64, Scheduler.new_with_cpu_count(2u32))
expect(validation.ok).to_be(false)
expect(validation.error).to_equal("handoff task not found")
expect(validation.pid).to_equal(701u64)
expect(validation.cr3).to_equal(0u64)
val context_present = if validation.context == nil: 0 else: 1
expect(context_present).to_equal(0)
```

</details>

#### creates a real scheduler user task through the spawn path

- creates a real scheduler user task through the spawn path
- build a real x86_64 user process image and create a scheduler user task
   - Expected: task_present equals `1`
   - Expected: created.entry_point equals `fixture.entry`
   - Expected: created.user_stack equals `fixture.stack_top`
   - Expected: created.address_space equals `fixture.cr3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("creates a real scheduler user task through the spawn path")
step("build a real x86_64 user process image and create a scheduler user task")
val fixture = build_spawn_fixture()
expect(fixture.pid).to_be_greater_than(0)
val task = fixture.scheduler.get_task(TaskId(id: fixture.pid))
val task_present = if task == nil: 0 else: 1
expect(task_present).to_equal(1)
if task != nil:
    val created = task
    expect(created.is_user).to_be(true)
    expect(created.entry_point).to_equal(fixture.entry)
    expect(created.user_stack).to_equal(fixture.stack_top)
    expect(created.address_space).to_equal(fixture.cr3)
```

</details>

#### accepts a real x86_64 user image handoff record without entering ring-3

- accepts a real x86_64 user image handoff record without entering ring-3
- create a scheduler user task through the real spawn path
- validate syscall-14 handoff readiness without executing the arch bridge
   - Expected: validation.error equals ``
   - Expected: validation.pid equals `fixture.pid`
   - Expected: validation.cr3 equals `fixture.cr3`
   - Expected: context_present equals `1`
   - Expected: ctx.rip equals `fixture.entry`
   - Expected: ctx.rsp equals `fixture.initial_sp`
   - Expected: ctx.cs equals `expected_ctx.cs`
   - Expected: ctx.ss equals `expected_ctx.ss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a real x86_64 user image handoff record without entering ring-3")
step("create a scheduler user task through the real spawn path")
val fixture = build_spawn_fixture()
expect(fixture.pid).to_be_greater_than(0)
val expected_ctx = scheduler_user_context_for_arch(sched_exec_arch(), fixture.entry, fixture.initial_sp)

step("validate syscall-14 handoff readiness without executing the arch bridge")
val validation = validate_enter_user_blocking_handoff(fixture.pid, fixture.scheduler)
expect(validation.ok).to_be(true)
expect(validation.error).to_equal("")
expect(validation.pid).to_equal(fixture.pid)
expect(validation.generation).to_be_greater_than(0u64)
expect(validation.cr3).to_equal(fixture.cr3)
val context_present = if validation.context == nil: 0 else: 1
expect(context_present).to_equal(1)
if validation.context != nil:
    val ctx = validation.context.unwrap()
    expect(ctx.rip).to_equal(fixture.entry)
    expect(ctx.rsp).to_equal(fixture.initial_sp)
    expect(ctx.cs).to_equal(expected_ctx.cs)
    expect(ctx.ss).to_equal(expected_ctx.ss)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba05d097d9a84575c09602ebce5964909cb776381c0bb205b7831d4146c8b9fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba05d097d9a84575c09602ebce5964909cb776381c0bb205b7831d4146c8b9fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba05d097d9a84575c09602ebce5964909cb776381c0bb205b7831d4146c8b9fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a missing user handoff task without entering ring-3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a real scheduler user task through the spawn path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a real x86_64 user image handoff record without entering ring-3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
