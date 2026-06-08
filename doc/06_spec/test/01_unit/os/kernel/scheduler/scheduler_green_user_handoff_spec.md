# Scheduler Green User Handoff Specification

> The green-carrier scheduler lane and the normal OS task lane must remain separate. This spec builds a real x86_64 user process image, creates a hosted scheduler task through `create_user_task_pid`, dispatches the pid through the green-carrier queue, and verifies that the user handoff record still exposes the same user context expected by syscall `14`.

<!-- sdn-diagram:id=scheduler_green_user_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_green_user_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_green_user_handoff_spec -> std
scheduler_green_user_handoff_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_green_user_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Green User Handoff Specification

The green-carrier scheduler lane and the normal OS task lane must remain separate. This spec builds a real x86_64 user process image, creates a hosted scheduler task through `create_user_task_pid`, dispatches the pid through the green-carrier queue, and verifies that the user handoff record still exposes the same user context expected by syscall `14`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The green-carrier scheduler lane and the normal OS task lane must remain
separate. This spec builds a real x86_64 user process image, creates a hosted
scheduler task through `create_user_task_pid`, dispatches the pid through the
green-carrier queue, and verifies that the user handoff record still exposes
the same user context expected by syscall `14`.

## Syntax

The executable scenario uses the same Pure Simple surfaces that the kernel path
uses before the hardware bridge:

```simple
scheduler.run_green_carrier_once(queues, cpu)
scheduler.get_user_handoff_task(pid)
validate_enter_user_blocking_handoff(pid, scheduler)
```

## Evidence Boundary

The spec proves scheduler/user-context compatibility and non-entering
EnterUserBlocking validation only. It does not execute `arch_x86_64_enter_user_task`
and cannot replace the final live QEMU AP ring/user marker triplet.

**Requirements:** doc/02_requirements/feature/multicore_green.md
**Plan:** doc/03_plan/sys_test/multicore_green.md
**Design:** doc/05_design/multicore_green.md
**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### Scheduler green user handoff

#### dispatches a real user handoff pid through the green lane

- build a real x86_64 user process image from executable bytes
- create a hosted scheduler user task through the real spawn path
- var sched = Scheduler new with cpu count
   - Expected: created_present equals `1`
   - Expected: created_task.entry_point equals `expected_entry`
   - Expected: created_task.user_stack equals `expected_stack_top`
   - Expected: created_task.address_space equals `expected_cr3`
   - Expected: created_ctx_present equals `1`
- dispatch that real user task through the green-carrier lane
   - Expected: step.dispatch.task_id equals `task_id.id as i64`
   - Expected: sched.green_current_task_on_cpu(1u32) equals `task_id.id`
   - Expected: sched.green_context_switches_on_cpu(1u32) equals `1`
   - Expected: sched.get_current_on_cpu(0u32).id equals `0`
- expose the scheduler user handoff record without synthetic task data
   - Expected: handoff_present equals `1`
   - Expected: task.id.id equals `task_id.id`
   - Expected: task.address_space equals `expected_cr3`
   - Expected: user_context_present equals `1`
   - Expected: user_ctx.rip equals `expected_entry`
   - Expected: user_ctx.rsp equals `expected_user_sp`
   - Expected: user_ctx.cs equals `expected_ctx.cs`
   - Expected: user_ctx.ss equals `expected_ctx.ss`
- validate the x86_64 EnterUserBlocking handoff without entering ring-3
   - Expected: validation.error equals ``
   - Expected: validation.pid equals `task_id.id`
   - Expected: validation.cr3 equals `expected_cr3`
   - Expected: validation_context_present equals `1`
   - Expected: validation_ctx.rip equals `expected_entry`
   - Expected: validation_ctx.rsp equals `expected_user_sp`
   - Expected: validation_ctx.cs equals `expected_ctx.cs`
   - Expected: validation_ctx.ss equals `expected_ctx.ss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 72 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a real x86_64 user process image from executable bytes")
val image_result = build_user_process_image("/sys/apps/green_ring3_probe", make_x86_64_exec(), Architecture.X86_64, [], [])
expect(image_result.is_ok()).to_be(true)
val image = image_result.unwrap()
val expected_entry = image.entry
val expected_user_sp = image.initial_sp & 0xFFFFFFFFFFFFFFF0
val expected_stack_top = image.stack_top

step("create a hosted scheduler user task through the real spawn path")
var sched = Scheduler.new_with_cpu_count(2u32)
val pid = sched.create_user_task_pid(image, TaskPriority.Normal, CapabilitySet.full())
expect(pid).to_be_greater_than(0)
val task_id = TaskId(id: pid)
val created = sched.get_task(task_id)
val created_present = if created == nil: 0 else: 1
expect(created_present).to_equal(1)
var expected_cr3: u64 = 0u64
if created != nil:
    val created_task = created
    expected_cr3 = created_task.address_space
    expect(created_task.is_user).to_be(true)
    expect(created_task.entry_point).to_equal(expected_entry)
    expect(created_task.user_stack).to_equal(expected_stack_top)
    expect(created_task.address_space).to_equal(expected_cr3)
    val created_ctx_present = if created_task.user_context == nil: 0 else: 1
    expect(created_ctx_present).to_equal(1)
val expected_ctx = scheduler_user_context_for_arch(sched_exec_arch(), expected_entry, expected_user_sp)

step("dispatch that real user task through the green-carrier lane")
val queues = green_carrier_run_queues_new(2, 4)
val decision = green_carrier_spawn_task(task_id.id as i64, 2, 2, 0, 1, 0, 0, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val step = sched.run_green_carrier_once(queued.queues, 1)

expect(step.ran).to_be(true)
expect(step.dispatch.task_id).to_equal(task_id.id as i64)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(task_id.id)
expect(sched.green_context_switches_on_cpu(1u32)).to_equal(1)
expect(sched.get_current_on_cpu(0u32).id).to_equal(0)

step("expose the scheduler user handoff record without synthetic task data")
val handoff = sched.get_user_handoff_task(task_id.id)
val handoff_present = if handoff == nil: 0 else: 1
expect(handoff_present).to_equal(1)
if handoff != nil:
    val task = handoff
    expect(task.id.id).to_equal(task_id.id)
    expect(task.is_user).to_be(true)
    expect(task.address_space).to_equal(expected_cr3)
    val user_context_present = if task.user_context == nil: 0 else: 1
    expect(user_context_present).to_equal(1)
    if task.user_context != nil:
        val user_ctx = task.user_context.unwrap()
        expect(user_ctx.rip).to_equal(expected_entry)
        expect(user_ctx.rsp).to_equal(expected_user_sp)
        expect(user_ctx.cs).to_equal(expected_ctx.cs)
        expect(user_ctx.ss).to_equal(expected_ctx.ss)

step("validate the x86_64 EnterUserBlocking handoff without entering ring-3")
val validation = validate_enter_user_blocking_handoff(task_id.id, sched)
expect(validation.ok).to_be(true)
expect(validation.error).to_equal("")
expect(validation.pid).to_equal(task_id.id)
expect(validation.cr3).to_equal(expected_cr3)
val validation_context_present = if validation.context == nil: 0 else: 1
expect(validation_context_present).to_equal(1)
if validation.context != nil:
    val validation_ctx = validation.context.unwrap()
    expect(validation_ctx.rip).to_equal(expected_entry)
    expect(validation_ctx.rsp).to_equal(expected_user_sp)
    expect(validation_ctx.cs).to_equal(expected_ctx.cs)
    expect(validation_ctx.ss).to_equal(expected_ctx.ss)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
