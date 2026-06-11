# SimpleOS Green Task Lifecycle Specification

> Tests the scheduler-facing logical green-task lifecycle used by future

<!-- sdn-diagram:id=green_task_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_task_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_task_spec -> std
green_task_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_task_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Task Lifecycle Specification

Tests the scheduler-facing logical green-task lifecycle used by future

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/scheduler/green_task_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests the scheduler-facing logical green-task lifecycle used by future
SimpleOS carrier workers.

## Scenarios

### SimpleOS green task lifecycle contract

### spawn

#### creates a runnable task on the least-loaded allowed CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(7, 4, 0, 3, 1, 2, 4)

expect(task.task_id).to_equal(7)
expect(task.home_cpu).to_equal(1)
expect(task.assigned_cpu).to_equal(1)
expect(task.state).to_equal("runnable")
expect(green_task_is_runnable(task)).to_equal(true)
```

</details>

#### preserves affinity placement from the worker contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_cpu2 = 1 << 2
val task = green_task_new(8, 4, only_cpu2, 0, 0, 9, 0)

expect(task.home_cpu).to_equal(2)
expect(task.assigned_cpu).to_equal(2)
expect(task.affinity_mask).to_equal(only_cpu2)
```

</details>

### park

#### parks a task without changing home or assigned CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(9, 4, 0, 0, 1, 2, 3)
val parked = green_task_park(task, "channel_recv")

expect(green_task_is_parked(parked)).to_equal(true)
expect(parked.state).to_equal("parked")
expect(parked.park_reason).to_equal("channel_recv")
expect(parked.home_cpu).to_equal(task.home_cpu)
expect(parked.assigned_cpu).to_equal(task.assigned_cpu)
```

</details>

### unpark

#### wakes a parked task onto the waker CPU when load is close

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(10, 4, 0, 0, 1, 2, 3)
val parked = green_task_park(task, "timer")
val wake = green_task_unpark(parked, 2, 2, 3, 1)

expect(wake.should_enqueue).to_equal(true)
expect(wake.task.state).to_equal("runnable")
expect(wake.task.assigned_cpu).to_equal(2)
expect(wake.placement.reason).to_equal("wake_affine_waker_cpu")
expect(wake.task.park_reason).to_equal("")
```

</details>

#### does not enqueue an already runnable task

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(11, 4, 0, 0, 1, 2, 3)
val wake = green_task_unpark(task, 2, 0, 0, 1)

expect(wake.should_enqueue).to_equal(false)
expect(wake.task.state).to_equal("runnable")
expect(wake.placement.reason).to_equal("not_parked")
```

</details>

### complete

#### marks a task done and keeps the last carrier CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = green_task_new(12, 4, 0, 3, 1, 2, 4)
val done = green_task_complete(task, 99)

expect(green_task_is_done(done)).to_equal(true)
expect(done.state).to_equal("done")
expect(done.result).to_equal(99)
expect(done.assigned_cpu).to_equal(task.assigned_cpu)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
