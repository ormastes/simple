# Scheduler Green User Handoff Specification

> Verifies the Pure Simple scheduler contract between the green-carrier lane and

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

Verifies the Pure Simple scheduler contract between the green-carrier lane and

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

Verifies the Pure Simple scheduler contract between the green-carrier lane and
the user-task handoff record before the architecture bridge. This is not final
x86_64 hardware handoff proof: final live QEMU evidence remains reserved for
`HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`
markers emitted from the real AP ring/user path.

## Scenarios

### Scheduler green user handoff

#### dispatches a real user handoff pid through the green lane

- var sched = seed user handoff task
   - Expected: step.ran is true
   - Expected: step.dispatch.task_id equals `pid as i64`
   - Expected: sched.green_current_task_on_cpu(1u32) equals `pid`
   - Expected: sched.green_context_switches_on_cpu(1u32) equals `1`
   - Expected: sched.get_current_on_cpu(0u32).id equals `0`
   - Expected: handoff == nil is false
   - Expected: task.id.id equals `pid`
   - Expected: task.is_user is true
   - Expected: task.user_context == nil is false
   - Expected: user_ctx.rip equals `0x400000`
   - Expected: user_ctx.rsp equals `0x3fffffff80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = 701u64
var sched = seed_user_handoff_task(Scheduler.new_with_cpu_count(2u32), pid, 0x400000, 0x3fffffff80)

val queues = green_carrier_run_queues_new(2, 4)
val decision = green_carrier_spawn_task(pid as i64, 2, 2, 0, 1, 0, 0, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val step = sched.run_green_carrier_once(queued.queues, 1)

expect(step.ran).to_equal(true)
expect(step.dispatch.task_id).to_equal(pid as i64)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(pid)
expect(sched.green_context_switches_on_cpu(1u32)).to_equal(1)
expect(sched.get_current_on_cpu(0u32).id).to_equal(0)

val handoff = sched.get_user_handoff_task(pid)
expect(handoff == nil).to_equal(false)
if handoff != nil:
    val task = handoff
    expect(task.id.id).to_equal(pid)
    expect(task.is_user).to_equal(true)
    expect(task.user_context == nil).to_equal(false)
    if task.user_context != nil:
        val user_ctx = task.user_context.unwrap()
        expect(user_ctx.rip).to_equal(0x400000)
        expect(user_ctx.rsp).to_equal(0x3fffffff80)
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
