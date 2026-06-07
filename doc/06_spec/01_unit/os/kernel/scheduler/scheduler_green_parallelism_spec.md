# Scheduler Green Carrier Parallelism Specification

> <details>

<!-- sdn-diagram:id=scheduler_green_parallelism_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_green_parallelism_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_green_parallelism_spec -> std
scheduler_green_parallelism_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_green_parallelism_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Green Carrier Parallelism Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Source | `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Scenarios

### Scheduler green carrier parallelism

#### starts from scheduler topology

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new_with_cpu_count(4u32)

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("default_topology_limit")
```

</details>

#### clamps requested carriers to scheduler topology

1. var sched = Scheduler new with cpu count
   - Expected: state.requested_limit equals `99`
   - Expected: state.active_limit equals `4`
   - Expected: state.reason equals `clamped_topology`
   - Expected: sched.green_carrier_parallelism_requested() equals `99`
   - Expected: sched.green_carrier_parallelism_limit() equals `4`
   - Expected: sched.green_carrier_parallelism_reason() equals `clamped_topology`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val state = sched.set_green_carrier_parallelism(99)

expect(state.requested_limit).to_equal(99)
expect(state.active_limit).to_equal(4)
expect(state.reason).to_equal("clamped_topology")
expect(sched.green_carrier_parallelism_requested()).to_equal(99)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("clamped_topology")
```

</details>

#### clamps zero or negative requested carriers through scheduler API

1. var sched = Scheduler new with cpu count
   - Expected: zero.requested_limit equals `0`
   - Expected: zero.active_limit equals `1`
   - Expected: zero.reason equals `clamped_min`
   - Expected: negative.requested_limit equals `-3`
   - Expected: negative.active_limit equals `1`
   - Expected: negative.reason equals `clamped_min`
   - Expected: sched.green_carrier_parallelism_requested() equals `-3`
   - Expected: sched.green_carrier_parallelism_limit() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val zero = sched.set_green_carrier_parallelism(0)
val negative = sched.set_green_carrier_parallelism(-3)

expect(zero.requested_limit).to_equal(0)
expect(zero.active_limit).to_equal(1)
expect(zero.reason).to_equal("clamped_min")
expect(negative.requested_limit).to_equal(-3)
expect(negative.active_limit).to_equal(1)
expect(negative.reason).to_equal("clamped_min")
expect(sched.green_carrier_parallelism_requested()).to_equal(-3)
expect(sched.green_carrier_parallelism_limit()).to_equal(1)
```

</details>

#### keeps requested carriers across topology changes

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism

3. sched set topology
   - Expected: sched.green_carrier_parallelism_requested() equals `4`
   - Expected: sched.green_carrier_parallelism_limit() equals `4`
   - Expected: sched.green_carrier_parallelism_reason() equals `requested_limit`

4. sched set topology
   - Expected: sched.green_carrier_parallelism_requested() equals `4`
   - Expected: sched.green_carrier_parallelism_limit() equals `1`
   - Expected: sched.green_carrier_parallelism_reason() equals `clamped_topology`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(2u32)
sched.set_green_carrier_parallelism(4)
sched.set_topology(default_scheduler_topology(4u32))

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("requested_limit")

sched.set_topology(default_scheduler_topology(1u32))

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(1)
expect(sched.green_carrier_parallelism_reason()).to_equal("clamped_topology")
```

</details>

#### keeps default carrier parallelism aligned to topology growth

1. var sched = Scheduler new bootstrap

2. sched set topology
   - Expected: sched.green_carrier_parallelism_requested() equals `4`
   - Expected: sched.green_carrier_parallelism_limit() equals `4`
   - Expected: sched.green_carrier_parallelism_reason() equals `default_topology_limit`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_bootstrap()
sched.set_topology(default_scheduler_topology(4u32))

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("default_topology_limit")
```

</details>

#### runs green dispatch on carriers activated by topology growth

1. var sched = Scheduler new bootstrap

2. sched set topology
   - Expected: result.applied is true
   - Expected: result.reason equals `context_switch_recorded`
   - Expected: sched.green_current_task_on_cpu(3u32) equals `52`
   - Expected: sched.green_rejected_intents() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_bootstrap()
sched.set_topology(default_scheduler_topology(4u32))
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(52, 4, 8, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 3)
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(result.applied).to_equal(true)
expect(result.reason).to_equal("context_switch_recorded")
expect(sched.green_current_task_on_cpu(3u32)).to_equal(52)
expect(sched.green_rejected_intents()).to_equal(0)
```

</details>

#### rejects green dispatch on inactive carriers

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: result.applied is false
   - Expected: result.reason equals `inactive_green_carrier`
   - Expected: dispatched.queues.queued_task_ids.len() equals `1`
   - Expected: green_carrier_dispatch_next(dispatched.queues, 1).task_id equals `51`
   - Expected: sched.green_current_task_on_cpu(1u32) equals `0`
   - Expected: sched.green_rejected_intents() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(51, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next_with_limit(queued.queues, 1, sched.green_carrier_parallelism_limit())
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(result.applied).to_equal(false)
expect(result.reason).to_equal("inactive_green_carrier")
expect(dispatched.queues.queued_task_ids.len()).to_equal(1)
expect(green_carrier_dispatch_next(dispatched.queues, 1).task_id).to_equal(51)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(0)
expect(sched.green_rejected_intents()).to_equal(1)
```

</details>

#### runs rebalanced inactive-carrier work on active carrier

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: moved.moved is true
   - Expected: dispatched.task_id equals `53`
   - Expected: result.applied is true
   - Expected: sched.green_current_task_on_cpu(0u32) equals `53`
   - Expected: sched.green_rejected_intents() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(53, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val rebalance = green_worker_rebalance_decision(4, 0, 4, 1, 2, 2)
val moved = sched.rebalance_green_carrier_queues(queued.queues, rebalance)
val dispatched = green_carrier_dispatch_next_with_limit(moved.queues, 0, sched.green_carrier_parallelism_limit())
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(moved.moved).to_equal(true)
expect(dispatched.task_id).to_equal(53)
expect(result.applied).to_equal(true)
expect(sched.green_current_task_on_cpu(0u32)).to_equal(53)
expect(sched.green_rejected_intents()).to_equal(0)
```

</details>

#### computes rebalance from carrier queue depths

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: moved.moved is true
   - Expected: moved.from_cpu equals `1`
   - Expected: moved.to_cpu equals `0`
   - Expected: result.applied is true
   - Expected: sched.green_current_task_on_cpu(0u32) equals `54`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(54, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val moved = sched.rebalance_green_carrier_queues_from_depth(queued.queues, 1)
val dispatched = green_carrier_dispatch_next_with_limit(moved.queues, 0, sched.green_carrier_parallelism_limit())
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(moved.moved).to_equal(true)
expect(moved.from_cpu).to_equal(1)
expect(moved.to_cpu).to_equal(0)
expect(result.applied).to_equal(true)
expect(sched.green_current_task_on_cpu(0u32)).to_equal(54)
```

</details>

#### drains inactive carrier queues with bounded repeated rebalance

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: pass_result.moved_workers equals `2`
   - Expected: pass_result.reason equals `inactive_sources_drained`
   - Expected: green_carrier_queue_depth(pass_result.queues, 1) equals `0`
   - Expected: green_carrier_queue_depth(pass_result.queues, 0) equals `2`
   - Expected: dispatch1.task_id equals `55`
   - Expected: dispatch2.task_id equals `56`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val first = green_carrier_spawn_task(55, 4, 0, 3, 1, 2, 4, 0)
val after_first = green_carrier_apply_enqueue(queues, first)
val second = green_carrier_spawn_task(56, 4, 0, 3, 1, 2, 4, 0)
val after_second = green_carrier_apply_enqueue(after_first.queues, second)
val pass_result = sched.rebalance_green_carrier_queues_until_stable(after_second.queues, 4)
val dispatch1 = green_carrier_dispatch_next_with_limit(pass_result.queues, 0, sched.green_carrier_parallelism_limit())
val dispatch2 = green_carrier_dispatch_next_with_limit(dispatch1.queues, 0, sched.green_carrier_parallelism_limit())

expect(pass_result.moved_workers).to_equal(2)
expect(pass_result.reason).to_equal("inactive_sources_drained")
expect(green_carrier_queue_depth(pass_result.queues, 1)).to_equal(0)
expect(green_carrier_queue_depth(pass_result.queues, 0)).to_equal(2)
expect(dispatch1.task_id).to_equal(55)
expect(dispatch2.task_id).to_equal(56)
```

</details>

#### honors repeated rebalance move budget

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: pass_result.moved_workers equals `1`
   - Expected: pass_result.reason equals `move_budget_exhausted`
   - Expected: green_carrier_queue_depth(pass_result.queues, 0) equals `1`
   - Expected: green_carrier_queue_depth(pass_result.queues, 1) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val first = green_carrier_spawn_task(57, 4, 0, 3, 1, 2, 4, 0)
val after_first = green_carrier_apply_enqueue(queues, first)
val second = green_carrier_spawn_task(58, 4, 0, 3, 1, 2, 4, 0)
val after_second = green_carrier_apply_enqueue(after_first.queues, second)
val pass_result = sched.rebalance_green_carrier_queues_until_stable(after_second.queues, 1)

expect(pass_result.moved_workers).to_equal(1)
expect(pass_result.reason).to_equal("move_budget_exhausted")
expect(green_carrier_queue_depth(pass_result.queues, 0)).to_equal(1)
expect(green_carrier_queue_depth(pass_result.queues, 1)).to_equal(1)
```

</details>

#### runs one active green carrier step through scheduler

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: step.ran is true
   - Expected: step.dispatch.task_id equals `59`
   - Expected: step.execution.applied is true
   - Expected: step.reason equals `context_switch_recorded`
   - Expected: sched.green_current_task_on_cpu(0u32) equals `59`
   - Expected: green_carrier_queue_depth(step.queues, 0) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(59, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val pass_result = sched.rebalance_green_carrier_queues_until_stable(queued.queues, 1)
val step = sched.run_green_carrier_once(pass_result.queues, 0)

expect(step.ran).to_equal(true)
expect(step.dispatch.task_id).to_equal(59)
expect(step.execution.applied).to_equal(true)
expect(step.reason).to_equal("context_switch_recorded")
expect(sched.green_current_task_on_cpu(0u32)).to_equal(59)
expect(green_carrier_queue_depth(step.queues, 0)).to_equal(0)
```

</details>

#### keeps queued work when scheduler run step targets inactive carrier

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism
   - Expected: step.ran is false
   - Expected: step.reason equals `inactive_green_carrier`
   - Expected: green_carrier_queue_depth(step.queues, 1) equals `1`
   - Expected: sched.green_current_task_on_cpu(1u32) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
sched.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(60, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val step = sched.run_green_carrier_once(queued.queues, 1)

expect(step.ran).to_equal(false)
expect(step.reason).to_equal("inactive_green_carrier")
expect(green_carrier_queue_depth(step.queues, 1)).to_equal(1)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)


</details>
