# SimpleOS Green Worker Scheduler Specification

> Tests the scheduler-facing placement rules for future SimpleOS green-task

<!-- sdn-diagram:id=green_worker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_worker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_worker_spec -> std
green_worker_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_worker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Worker Scheduler Specification

Tests the scheduler-facing placement rules for future SimpleOS green-task

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/scheduler/green_worker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests the scheduler-facing placement rules for future SimpleOS green-task
carrier workers.

## Scenarios

### SimpleOS green worker scheduler contract

### CPU affinity

#### allows every CPU when affinity mask is zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(green_worker_cpu_allowed(0, 0)).to_equal(true)
expect(green_worker_cpu_allowed(0, 3)).to_equal(true)
expect(green_worker_cpu_allowed(0, -1)).to_equal(false)
```

</details>

#### restricts workers to CPUs present in the affinity mask

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu1_and_cpu3 = (1 << 1) | (1 << 3)

expect(green_worker_cpu_allowed(cpu1_and_cpu3, 0)).to_equal(false)
expect(green_worker_cpu_allowed(cpu1_and_cpu3, 1)).to_equal(true)
expect(green_worker_cpu_allowed(cpu1_and_cpu3, 3)).to_equal(true)
```

</details>

### spawn placement

#### chooses the least-loaded allowed CPU

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val placement = green_worker_pick_spawn_cpu(4, 0, 3, 1, 2, 4)

expect(placement.cpu).to_equal(1)
expect(placement.reason).to_equal("least_loaded_allowed_cpu")
```

</details>

#### honors affinity before load when placing a worker

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_cpu2 = 1 << 2
val placement = green_worker_pick_spawn_cpu(4, only_cpu2, 0, 0, 9, 0)

expect(placement.cpu).to_equal(2)
```

</details>

### wake placement

#### uses the waker CPU when affinity allows it and load is close

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val placement = green_worker_choose_wake_cpu(0, 1, 0, 2, 3, 1)

expect(placement.cpu).to_equal(1)
expect(placement.reason).to_equal("wake_affine_waker_cpu")
```

</details>

#### falls back to home CPU when the waker CPU is overloaded

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val placement = green_worker_choose_wake_cpu(0, 1, 0, 1, 5, 1)

expect(placement.cpu).to_equal(0)
expect(placement.reason).to_equal("home_cpu")
```

</details>

#### uses the first allowed CPU when home and waker CPUs are disallowed

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val only_cpu2 = 1 << 2
val placement = green_worker_choose_wake_cpu(0, 1, only_cpu2, 0, 0, 1)

expect(placement.cpu).to_equal(2)
expect(placement.reason).to_equal("first_allowed_cpu")
```

</details>

### stealing and rebalancing

#### steals only when remote load crosses the threshold

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(green_worker_should_steal(1, 4, 2)).to_equal(true)
expect(green_worker_should_steal(2, 3, 2)).to_equal(false)
```

</details>

#### moves one worker from busiest CPU to idlest CPU

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = green_worker_rebalance_decision(4, 0, 4, 1, 2, 2)

expect(decision.should_move).to_equal(true)
expect(decision.from_cpu).to_equal(1)
expect(decision.to_cpu).to_equal(0)
expect(decision.moved_workers).to_equal(1)
expect(decision.reason).to_equal("busiest_to_idlest")
```

</details>

#### does not rebalance below threshold

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = green_worker_rebalance_decision(4, 2, 3, 2, 2, 2)

expect(decision.should_move).to_equal(false)
expect(decision.moved_workers).to_equal(0)
expect(decision.reason).to_equal("below_threshold")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
