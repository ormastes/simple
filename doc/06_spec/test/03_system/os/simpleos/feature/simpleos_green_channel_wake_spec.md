# SimpleOS Green Channel Wake System Contract

> This system spec connects the pure green-channel contract to the SimpleOS green-carrier scheduler bridge. A receive on an empty green channel parks a logical green task id. A later send reports the receiver to unpark, and the carrier bridge must convert that wake into a normal green enqueue, dispatch, and scheduler-owned execution-state update.

<!-- sdn-diagram:id=simpleos_green_channel_wake_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_green_channel_wake_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_green_channel_wake_spec -> std
simpleos_green_channel_wake_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_green_channel_wake_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Green Channel Wake System Contract

This system spec connects the pure green-channel contract to the SimpleOS green-carrier scheduler bridge. A receive on an empty green channel parks a logical green task id. A later send reports the receiver to unpark, and the carrier bridge must convert that wake into a normal green enqueue, dispatch, and scheduler-owned execution-state update.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-channel-wake |
| Category | SimpleOS / Concurrency |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec connects the pure green-channel contract to the SimpleOS
green-carrier scheduler bridge. A receive on an empty green channel parks a
logical green task id. A later send reports the receiver to unpark, and the
carrier bridge must convert that wake into a normal green enqueue, dispatch,
and scheduler-owned execution-state update.

The spec is hosted and deterministic. Live guest/AP execution remains covered
by the QEMU SMP proof item in the multicore-green plan.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

The bridge consumes `green_channel_send(...).receiver_task_id` and
`green_channel_send(...).unparked`, then calls
`green_carrier_channel_wake_task(...)` before the normal
`green_carrier_apply_enqueue` / dispatch / scheduler-intent flow.

## Examples

```simple
val parked_recv = green_channel_recv(channel, parked_task.task_id)
val sent = green_channel_send(parked_recv.channel, 77)
val decision = green_carrier_channel_wake_task(parked_task, sent.receiver_task_id, sent.unparked, 2, 2, 3, 1, 0)
```

## Scenarios

### SimpleOS green channel wake contract

#### runs a channel wake through the scheduler-owned active pass

- smp init
- smp bringup ap
- var scheduler = Scheduler new with cpu count
- scheduler set green carrier parallelism
   - Expected: sent.unparked is true
   - Expected: wake.enqueued is true
   - Expected: wake.apply.decision.target_cpu equals `2`
   - Expected: wake.apply.ipi_sent is true
   - Expected: pending equals `smp_ipi_resched()`
   - Expected: wake.pass_result.rebalance.moved_workers equals `1`
   - Expected: wake.pass_result.ran_workers equals `1`
   - Expected: wake.ran is true
   - Expected: wake.reason equals `active_pass_ran`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `504`
   - Expected: scheduler.green_current_task_on_cpu(2u32) equals `0`
   - Expected: green_carrier_queue_depth(wake.queues, 0) equals `0`
   - Expected: green_carrier_queue_depth(wake.queues, 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(2u32)
var scheduler = Scheduler.new_with_cpu_count(4u32)
scheduler.set_green_carrier_parallelism(1)
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(504, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, parked_task.task_id)
val sent = green_channel_send(parked_recv.channel, 77)
val wake = scheduler.run_green_channel_wake_pass(
    queues,
    parked_task,
    sent.receiver_task_id,
    sent.unparked,
    2,
    2,
    3,
    1,
    0,
    1
)
val pending = smp_take_ipi(2u32)

expect(sent.unparked).to_equal(true)
expect(wake.enqueued).to_equal(true)
expect(wake.apply.decision.target_cpu).to_equal(2)
expect(wake.apply.ipi_sent).to_equal(true)
expect(pending).to_equal(smp_ipi_resched())
expect(wake.pass_result.rebalance.moved_workers).to_equal(1)
expect(wake.pass_result.ran_workers).to_equal(1)
expect(wake.ran).to_equal(true)
expect(wake.reason).to_equal("active_pass_ran")
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(504)
expect(scheduler.green_current_task_on_cpu(2u32)).to_equal(0)
expect(green_carrier_queue_depth(wake.queues, 0)).to_equal(0)
expect(green_carrier_queue_depth(wake.queues, 2)).to_equal(0)
```

</details>

#### re-enqueues an unparked channel receiver through carrier dispatch

- smp init
- smp bringup ap
- var scheduler = Scheduler new with cpu count
   - Expected: sent.unparked is true
   - Expected: decision.should_enqueue is true
   - Expected: decision.target_cpu equals `2`
   - Expected: decision.reason equals `wake_affine_waker_cpu`
   - Expected: applied.enqueued is true
   - Expected: applied.ipi_sent is true
   - Expected: pending equals `smp_ipi_resched()`
   - Expected: green_carrier_queue_depth(applied.queues, 2) equals `1`
   - Expected: dispatched.dispatched is true
   - Expected: dispatched.task_id equals `501`
   - Expected: scheduled.applied is true
   - Expected: scheduler.green_current_task_on_cpu(2u32) equals `501`
   - Expected: scheduler.green_context_switches_on_cpu(2u32) equals `1`
   - Expected: scheduler.get_current_on_cpu(2u32).id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(2u32)
var scheduler = Scheduler.new_with_cpu_count(4u32)
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(501, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, parked_task.task_id)
val sent = green_channel_send(parked_recv.channel, 77)
val decision = green_carrier_channel_wake_task(
    parked_task,
    sent.receiver_task_id,
    sent.unparked,
    2,
    2,
    3,
    1,
    0
)
val applied = green_carrier_apply_enqueue(queues, decision)
val pending = smp_take_ipi(2u32)
val dispatched = green_carrier_dispatch_next(applied.queues, 2)
val scheduled = scheduler.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(sent.unparked).to_equal(true)
expect(decision.should_enqueue).to_equal(true)
expect(decision.target_cpu).to_equal(2)
expect(decision.reason).to_equal("wake_affine_waker_cpu")
expect(applied.enqueued).to_equal(true)
expect(applied.ipi_sent).to_equal(true)
expect(pending).to_equal(smp_ipi_resched())
expect(green_carrier_queue_depth(applied.queues, 2)).to_equal(1)
expect(dispatched.dispatched).to_equal(true)
expect(dispatched.task_id).to_equal(501)
expect(scheduled.applied).to_equal(true)
expect(scheduler.green_current_task_on_cpu(2u32)).to_equal(501)
expect(scheduler.green_context_switches_on_cpu(2u32)).to_equal(1)
expect(scheduler.get_current_on_cpu(2u32).id).to_equal(0)
```

</details>

#### does not enqueue when a send buffered without waking a receiver

- smp init
   - Expected: sent.unparked is false
   - Expected: decision.should_enqueue is false
   - Expected: decision.reason equals `channel_no_receiver`
   - Expected: applied.enqueued is false
   - Expected: applied.queues.queued_task_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(502, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val sent = green_channel_send(green_channel_new(1), 88)
val decision = green_carrier_channel_wake_task(
    parked_task,
    sent.receiver_task_id,
    sent.unparked,
    2,
    2,
    3,
    1,
    0
)
val applied = green_carrier_apply_enqueue(queues, decision)

expect(sent.unparked).to_equal(false)
expect(decision.should_enqueue).to_equal(false)
expect(decision.reason).to_equal("channel_no_receiver")
expect(applied.enqueued).to_equal(false)
expect(applied.queues.queued_task_ids.len()).to_equal(0)
```

</details>

#### rejects mismatched channel wake task ids

- smp init
   - Expected: sent.unparked is true
   - Expected: sent.receiver_task_id equals `999`
   - Expected: decision.should_enqueue is false
   - Expected: decision.reason equals `channel_receiver_mismatch`
   - Expected: applied.enqueued is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(503, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, 999)
val sent = green_channel_send(parked_recv.channel, 99)
val decision = green_carrier_channel_wake_task(
    parked_task,
    sent.receiver_task_id,
    sent.unparked,
    2,
    2,
    3,
    1,
    0
)
val applied = green_carrier_apply_enqueue(queues, decision)

expect(sent.unparked).to_equal(true)
expect(sent.receiver_task_id).to_equal(999)
expect(decision.should_enqueue).to_equal(false)
expect(decision.reason).to_equal("channel_receiver_mismatch")
expect(applied.enqueued).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
