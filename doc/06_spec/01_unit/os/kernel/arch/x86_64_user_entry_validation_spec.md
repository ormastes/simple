# x86_64 User Entry Validation Specification

> SimpleOS needs a final live QEMU proof for AP green-carrier ring/user handoff, but hosted tests must not execute the x86_64 `iretq` user-entry bridge. This spec covers the safe prerequisite: the scheduler can expose a user handoff TCB with a valid user context and CR3 value, and the syscall-14 validation layer can accept or reject that record before the architecture bridge runs.

<!-- sdn-diagram:id=x86_64_user_entry_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_user_entry_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_user_entry_validation_spec -> std
x86_64_user_entry_validation_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_user_entry_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- validate an empty scheduler
   - Expected: validation.error equals `handoff task not found`
   - Expected: validation.pid equals `701u64`
   - Expected: validation.cr3 equals `0u64`
   - Expected: context_present equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- build a real x86_64 user process image and create a scheduler user task
   - Expected: task_present equals `1`
   - Expected: created.entry_point equals `fixture.entry`
   - Expected: created.user_stack equals `fixture.stack_top`
   - Expected: created.address_space equals `fixture.cr3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("create a scheduler user task through the real spawn path")
val fixture = build_spawn_fixture()
expect(fixture.pid).to_be_greater_than(0)
val expected_ctx = scheduler_user_context_for_arch(sched_exec_arch(), fixture.entry, fixture.initial_sp)

step("validate syscall-14 handoff readiness without executing the arch bridge")
val validation = validate_enter_user_blocking_handoff(fixture.pid, fixture.scheduler)
expect(validation.ok).to_be(true)
expect(validation.error).to_equal("")
expect(validation.pid).to_equal(fixture.pid)
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

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
