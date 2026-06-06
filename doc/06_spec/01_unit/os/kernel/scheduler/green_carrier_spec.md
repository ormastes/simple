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
| 7 | 7 | 0 | 0 |

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

This keeps the SimpleOS side testable before the real run-queue and wakeup
hooks are connected. The contract also prevents parked or completed green tasks
from being re-enqueued by mistake.

## Examples

Spawning a logical green task chooses a CPU through the existing green-worker
placement rules and turns the runnable task into either a local or remote
carrier enqueue decision. Waking a parked green task reuses the green-task
unpark decision, then records whether the chosen CPU is remote to the current
carrier CPU.

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
