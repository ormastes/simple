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
| 11 | 11 | 0 | 0 |

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
existing SimpleOS SMP reschedule IPI surface for remote online CPUs.

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
