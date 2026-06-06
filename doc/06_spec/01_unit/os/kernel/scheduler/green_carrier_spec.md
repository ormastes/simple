# SimpleOS Green Carrier Bridge Specification

> The carrier bridge is the contract between pure logical green-task state and the lower SimpleOS scheduler work that will eventually insert runnable green tasks into per-CPU queues. It does not execute closures and it does not send APIC interrupts directly. Instead, it records the target carrier CPU, whether a green task should be enqueued, and whether a remote reschedule IPI is required.

<!-- sdn-diagram:id=green_carrier_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_carrier_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_carrier_spec -> std
green_carrier_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_carrier_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Carrier Bridge Specification

The carrier bridge is the contract between pure logical green-task state and the lower SimpleOS scheduler work that will eventually insert runnable green tasks into per-CPU queues. It does not execute closures and it does not send APIC interrupts directly. Instead, it records the target carrier CPU, whether a green task should be enqueued, and whether a remote reschedule IPI is required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The carrier bridge is the contract between pure logical green-task state and the
lower SimpleOS scheduler work that will eventually insert runnable green tasks
into per-CPU queues. It does not execute closures and it does not send APIC
interrupts directly. Instead, it records the target carrier CPU, whether a
green task should be enqueued, and whether a remote reschedule IPI is required.

This keeps the SimpleOS side testable while the green carrier path moves from
decision-only contracts toward concrete queue mutation and wakeup hooks. The
contract also prevents parked or completed green tasks from being re-enqueued
by mistake.

## Examples

Spawning a logical green task chooses a CPU through the existing green-worker
placement rules and turns the runnable task into either a local or remote
carrier enqueue decision. Waking a parked green task reuses the green-task
unpark decision, then records whether the chosen CPU is remote to the current
carrier CPU. Applying a decision updates bounded carrier queues and uses the
existing SimpleOS SMP reschedule IPI surface for remote online CPUs. Dispatch
selects queued work for a carrier CPU without stealing tasks from other CPUs.
The scheduler intent step converts successful dispatch into a typed `TaskId`
and a context-switch request, while failed dispatches remain no-op scheduler
intents. Applying the intent records the current green task and switch count for
the target carrier CPU without performing the hardware context switch itself;
that keeps the contract executable before QEMU SMP context-switch evidence.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### SimpleOS green carrier bridge contract

### spawn enqueue

#### enqueues a new runnable task onto the selected carrier CPU

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = green_carrier_spawn_task(21, 4, 0, 3, 1, 2, 4, 1)

expect(decision.task.task_id).to_equal(21)
expect(decision.target_cpu).to_equal(1)
expect(decision.should_enqueue).to_equal(true)
expect(decision.should_send_ipi).to_equal(false)
expect(decision.reason).to_equal("local_run_queue")
```

</details>

#### requests a reschedule IPI for remote run-queue enqueue

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = green_carrier_spawn_task(22, 4, 0, 3, 1, 2, 4, 0)

expect(decision.target_cpu).to_equal(1)
expect(decision.should_enqueue).to_equal(true)
expect(decision.should_send_ipi).to_equal(true)
expect(decision.ipi_reason).to_equal("remote_reschedule")
expect(decision.reason).to_equal("remote_run_queue")
```

</details>

### wake enqueue

#### wakes a parked task onto the waker CPU when load is close

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(23, 4, 0, 0, 1, 2, 3)
val parked = green_task_park(task, "channel_recv")
val decision = green_carrier_unpark_task(parked, 2, 2, 3, 1, 0)

expect(decision.task.state).to_equal("runnable")
expect(decision.target_cpu).to_equal(2)
expect(decision.should_enqueue).to_equal(true)
expect(decision.should_send_ipi).to_equal(true)
expect(decision.reason).to_equal("wake_affine_waker_cpu")
```

</details>

#### does not enqueue when unpark is misused on a runnable task

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(24, 4, 0, 0, 1, 2, 3)
val decision = green_carrier_unpark_task(task, 2, 0, 0, 1, 0)

expect(decision.task.state).to_equal("runnable")
expect(decision.should_enqueue).to_equal(false)
expect(decision.should_send_ipi).to_equal(false)
expect(decision.reason).to_equal("not_parked")
```

</details>

### blocked states

#### does not enqueue parked tasks directly

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(25, 4, 0, 0, 1, 2, 3)
val parked = green_task_park(task, "timer")
val decision = green_carrier_enqueue_task(parked, 0)

expect(decision.should_enqueue).to_equal(false)
expect(decision.should_send_ipi).to_equal(false)
expect(decision.reason).to_equal("task_parked")
```

</details>

#### does not enqueue completed tasks

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(26, 4, 0, 0, 1, 2, 3)
val done = green_task_complete(task, 77)
val decision = green_carrier_enqueue_task(done, 0)

expect(decision.task.result).to_equal(77)
expect(decision.should_enqueue).to_equal(false)
expect(decision.should_send_ipi).to_equal(false)
expect(decision.reason).to_equal("task_done")
```

</details>

### IPI guard

#### sends IPI only for remote runnable enqueue

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(green_carrier_should_send_ipi(0, 1, true)).to_equal(true)
expect(green_carrier_should_send_ipi(1, 1, true)).to_equal(false)
expect(green_carrier_should_send_ipi(0, 1, false)).to_equal(false)
```

</details>

### queue apply

#### applies local enqueue into the carrier run queue without IPI

1. smp init
   - Expected: applied.enqueued is true
   - Expected: applied.ipi_sent is false
   - Expected: applied.reason equals `queued_local`
   - Expected: green_carrier_queue_depth(applied.queues, 1) equals `1`
   - Expected: applied.queues.queued_task_ids.len() equals `1`
   - Expected: applied.queues.queued_task_ids[0] equals `27`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(27, 4, 0, 3, 1, 2, 4, 1)
val applied = green_carrier_apply_enqueue(queues, decision)

expect(applied.enqueued).to_equal(true)
expect(applied.ipi_sent).to_equal(false)
expect(applied.reason).to_equal("queued_local")
expect(green_carrier_queue_depth(applied.queues, 1)).to_equal(1)
expect(applied.queues.queued_task_ids.len()).to_equal(1)
expect(applied.queues.queued_task_ids[0]).to_equal(27)
```

</details>

#### applies remote enqueue and records a SimpleOS reschedule IPI

1. smp init

2. smp bringup ap
   - Expected: applied.enqueued is true
   - Expected: applied.ipi_sent is true
   - Expected: applied.ipi_reason_mask equals `0x1u32`
   - Expected: pending equals `0x1u32`
   - Expected: green_carrier_queue_depth(applied.queues, 1) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(1u32)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(28, 4, 0, 3, 1, 2, 4, 0)
val applied = green_carrier_apply_enqueue(queues, decision)
val pending = smp_take_ipi(1u32)

expect(applied.enqueued).to_equal(true)
expect(applied.ipi_sent).to_equal(true)
expect(applied.ipi_reason_mask).to_equal(0x1u32)
expect(pending).to_equal(0x1u32)
expect(green_carrier_queue_depth(applied.queues, 1)).to_equal(1)
```

</details>

#### does not mutate queues for non-enqueue decisions

1. smp init
   - Expected: applied.enqueued is false
   - Expected: applied.queues.queued_task_ids.len() equals `0`
   - Expected: applied.reason equals `task_parked`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val task = green_task_new(29, 4, 0, 0, 1, 2, 3)
val parked = green_task_park(task, "timer")
val decision = green_carrier_enqueue_task(parked, 0)
val queues = green_carrier_run_queues_new(4, 8)
val applied = green_carrier_apply_enqueue(queues, decision)

expect(applied.enqueued).to_equal(false)
expect(applied.queues.queued_task_ids.len()).to_equal(0)
expect(applied.reason).to_equal("task_parked")
```

</details>

#### rejects enqueue when the green carrier queue is full

1. smp init
   - Expected: after_first.enqueued is true
   - Expected: after_second.enqueued is false
   - Expected: after_second.reason equals `queue_rejected`
   - Expected: after_second.queues.dropped_count equals `1`
   - Expected: after_second.queues.queued_task_ids.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 1)
val first = green_carrier_spawn_task(30, 4, 0, 3, 1, 2, 4, 1)
val after_first = green_carrier_apply_enqueue(queues, first)
val second = green_carrier_spawn_task(31, 4, 0, 3, 1, 2, 4, 1)
val after_second = green_carrier_apply_enqueue(after_first.queues, second)

expect(after_first.enqueued).to_equal(true)
expect(after_second.enqueued).to_equal(false)
expect(after_second.reason).to_equal("queue_rejected")
expect(after_second.queues.dropped_count).to_equal(1)
expect(after_second.queues.queued_task_ids.len()).to_equal(1)
```

</details>

### dispatch

#### dispatches queued green work for the requested carrier CPU

1. smp init
   - Expected: dispatched.dispatched is true
   - Expected: dispatched.task_id equals `32`
   - Expected: dispatched.cpu equals `1`
   - Expected: dispatched.reason equals `dispatched`
   - Expected: green_carrier_queue_depth(dispatched.queues, 1) equals `0`
   - Expected: dispatched.queues.queued_task_ids.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val first = green_carrier_spawn_task(32, 4, 0, 3, 1, 2, 4, 1)
val queued = green_carrier_apply_enqueue(queues, first)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)

expect(dispatched.dispatched).to_equal(true)
expect(dispatched.task_id).to_equal(32)
expect(dispatched.cpu).to_equal(1)
expect(dispatched.reason).to_equal("dispatched")
expect(green_carrier_queue_depth(dispatched.queues, 1)).to_equal(0)
expect(dispatched.queues.queued_task_ids.len()).to_equal(0)
```

</details>

#### preserves queued work for other carrier CPUs

1. smp init
   - Expected: dispatched.dispatched is true
   - Expected: dispatched.task_id equals `33`
   - Expected: green_carrier_queue_depth(dispatched.queues, 1) equals `0`
   - Expected: green_carrier_queue_depth(dispatched.queues, 2) equals `1`
   - Expected: dispatched.queues.queued_task_ids.len() equals `1`
   - Expected: dispatched.queues.queued_task_ids[0] equals `34`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val cpu1_task = green_carrier_spawn_task(33, 4, 0, 3, 1, 2, 4, 1)
val after_cpu1 = green_carrier_apply_enqueue(queues, cpu1_task)
val cpu2_task = green_carrier_spawn_task(34, 4, 0, 3, 4, 1, 2, 2)
val after_cpu2 = green_carrier_apply_enqueue(after_cpu1.queues, cpu2_task)
val dispatched = green_carrier_dispatch_next(after_cpu2.queues, 1)

expect(dispatched.dispatched).to_equal(true)
expect(dispatched.task_id).to_equal(33)
expect(green_carrier_queue_depth(dispatched.queues, 1)).to_equal(0)
expect(green_carrier_queue_depth(dispatched.queues, 2)).to_equal(1)
expect(dispatched.queues.queued_task_ids.len()).to_equal(1)
expect(dispatched.queues.queued_task_ids[0]).to_equal(34)
```

</details>

#### reports empty queue without mutating state

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queues = green_carrier_run_queues_new(4, 8)
val dispatched = green_carrier_dispatch_next(queues, 1)

expect(dispatched.dispatched).to_equal(false)
expect(dispatched.task_id).to_equal(-1)
expect(dispatched.reason).to_equal("queue_empty")
expect(dispatched.queues.queued_task_ids.len()).to_equal(0)
```

</details>

#### rejects dispatch for invalid carrier CPU

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queues = green_carrier_run_queues_new(4, 8)
val dispatched = green_carrier_dispatch_next(queues, 9)

expect(dispatched.dispatched).to_equal(false)
expect(dispatched.task_id).to_equal(-1)
expect(dispatched.reason).to_equal("invalid_cpu")
```

</details>

### scheduler intent

#### converts successful dispatch into a typed scheduler run intent

1. smp init
   - Expected: intent.should_run is true
   - Expected: intent.should_context_switch is true
   - Expected: intent.task.id equals `35`
   - Expected: intent.cpu equals `1u32`
   - Expected: intent.reason equals `green_task_ready`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(35, 4, 0, 3, 1, 2, 4, 1)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
val intent = green_carrier_scheduler_intent(dispatched)

expect(intent.should_run).to_equal(true)
expect(intent.should_context_switch).to_equal(true)
expect(intent.task.id).to_equal(35)
expect(intent.cpu).to_equal(1u32)
expect(intent.reason).to_equal("green_task_ready")
```

</details>

#### keeps empty dispatch as a no-op scheduler intent

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queues = green_carrier_run_queues_new(4, 8)
val dispatched = green_carrier_dispatch_next(queues, 1)
val intent = green_carrier_scheduler_intent(dispatched)

expect(intent.should_run).to_equal(false)
expect(intent.should_context_switch).to_equal(false)
expect(intent.task.id).to_equal(0)
expect(intent.cpu).to_equal(1u32)
expect(intent.reason).to_equal("queue_empty")
```

</details>

### execution apply

#### extends execution state for additional carrier CPUs

1. green carrier run queues new

2. green carrier spawn task
   - Expected: applied.applied is true
   - Expected: green_carrier_current_task_on_cpu(applied.state, 3) equals `39`
   - Expected: green_carrier_context_switches_on_cpu(applied.state, 3) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = green_carrier_execution_state_new(1)
val extended = green_carrier_extend_execution_state(state, 4)
val intent = green_carrier_scheduler_intent(
    green_carrier_dispatch_next(
        green_carrier_apply_enqueue(
            green_carrier_run_queues_new(4, 8),
            green_carrier_spawn_task(39, 4, 8, 3, 1, 2, 4, 0)
        ).queues,
        3
    )
)
val applied = green_carrier_apply_scheduler_intent(extended, intent)

expect(applied.applied).to_equal(true)
expect(green_carrier_current_task_on_cpu(applied.state, 3)).to_equal(39)
expect(green_carrier_context_switches_on_cpu(applied.state, 3)).to_equal(1)
```

</details>

#### records current green task and switch count for scheduler intent

1. smp init
   - Expected: applied.applied is true
   - Expected: applied.reason equals `context_switch_recorded`
   - Expected: green_carrier_current_task_on_cpu(applied.state, 1) equals `36`
   - Expected: green_carrier_context_switches_on_cpu(applied.state, 1) equals `1`
   - Expected: applied.state.total_context_switches equals `1`
   - Expected: applied.state.rejected_intents equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(36, 4, 0, 3, 1, 2, 4, 1)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
val intent = green_carrier_scheduler_intent(dispatched)
val state = green_carrier_execution_state_new(4)
val applied = green_carrier_apply_scheduler_intent(state, intent)

expect(applied.applied).to_equal(true)
expect(applied.reason).to_equal("context_switch_recorded")
expect(green_carrier_current_task_on_cpu(applied.state, 1)).to_equal(36)
expect(green_carrier_context_switches_on_cpu(applied.state, 1)).to_equal(1)
expect(applied.state.total_context_switches).to_equal(1)
expect(applied.state.rejected_intents).to_equal(0)
```

</details>

#### rejects no-op intent without changing current task

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queues = green_carrier_run_queues_new(4, 8)
val dispatched = green_carrier_dispatch_next(queues, 2)
val intent = green_carrier_scheduler_intent(dispatched)
val state = green_carrier_execution_state_new(4)
val applied = green_carrier_apply_scheduler_intent(state, intent)

expect(applied.applied).to_equal(false)
expect(applied.reason).to_equal("queue_empty")
expect(green_carrier_current_task_on_cpu(applied.state, 2)).to_equal(0)
expect(green_carrier_context_switches_on_cpu(applied.state, 2)).to_equal(0)
expect(applied.state.rejected_intents).to_equal(1)
```

</details>

#### keeps execution state isolated per carrier CPU

1. smp init
   - Expected: green_carrier_current_task_on_cpu(apply2.state, 1) equals `37`
   - Expected: green_carrier_current_task_on_cpu(apply2.state, 2) equals `38`
   - Expected: green_carrier_context_switches_on_cpu(apply2.state, 1) equals `1`
   - Expected: green_carrier_context_switches_on_cpu(apply2.state, 2) equals `1`
   - Expected: apply2.state.total_context_switches equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val cpu1_task = green_carrier_spawn_task(37, 4, 0, 3, 1, 2, 4, 1)
val after_cpu1 = green_carrier_apply_enqueue(queues, cpu1_task)
val cpu2_task = green_carrier_spawn_task(38, 4, 0, 3, 4, 1, 2, 2)
val after_cpu2 = green_carrier_apply_enqueue(after_cpu1.queues, cpu2_task)
val state = green_carrier_execution_state_new(4)
val dispatch1 = green_carrier_dispatch_next(after_cpu2.queues, 1)
val apply1 = green_carrier_apply_scheduler_intent(state, green_carrier_scheduler_intent(dispatch1))
val dispatch2 = green_carrier_dispatch_next(dispatch1.queues, 2)
val apply2 = green_carrier_apply_scheduler_intent(apply1.state, green_carrier_scheduler_intent(dispatch2))

expect(green_carrier_current_task_on_cpu(apply2.state, 1)).to_equal(37)
expect(green_carrier_current_task_on_cpu(apply2.state, 2)).to_equal(38)
expect(green_carrier_context_switches_on_cpu(apply2.state, 1)).to_equal(1)
expect(green_carrier_context_switches_on_cpu(apply2.state, 2)).to_equal(1)
expect(apply2.state.total_context_switches).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
