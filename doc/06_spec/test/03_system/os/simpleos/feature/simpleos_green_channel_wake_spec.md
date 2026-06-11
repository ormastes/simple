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

## Manual Evidence

This manual is meant to be readable without opening the executable SSpec. The
scenario validates four hosted SimpleOS wake paths:

- A parked receiver wakes and runs through the scheduler-owned active carrier
  pass.
- A parked receiver wakes and re-enters scheduler-owned green execution state
  through explicit carrier dispatch.
- A buffered send with no parked receiver does not enqueue carrier work.
- A wake for the wrong receiver id is rejected before queue mutation.

The important distinction is that `green_channel_send` only reports wake
metadata. SimpleOS owns the conversion from wake metadata to carrier enqueue,
remote reschedule IPI, dispatch, and scheduler intent application.

## TUI Capture

The following text capture is the expected operator view for the successful
wake path:

```text
SimpleOS Green Channel Wake
---------------------------
channel: bounded(1)
parked receiver task: 504
send value: 77
unparked: true
target carrier cpu: 2
remote enqueue: true
reschedule ipi: sent
active carrier pass: ran
rebalance moved workers: 1
cpu0 green current: 504
cpu2 green current: 0
queue depth cpu0: 0
queue depth cpu2: 0
result: wake bridged into scheduler-owned green state
```

The rejection paths should read differently:

```text
SimpleOS Green Channel Wake
---------------------------
no receiver: channel_no_receiver
mismatched receiver: channel_receiver_mismatch
remote enqueue: false
queue mutation: none
```

## Expected Results

- `sent.unparked` is true only when a receiver was parked on the channel.
- `decision.should_enqueue` is true only when the receiver id matches the parked
  green task id.
- `applied.ipi_sent` is true only for a remote carrier enqueue.
- `scheduler.green_current_task_on_cpu(...)` records green execution separately
  from the normal OS task slot.
- Queue depths return to zero after the active carrier pass consumes the wake.

## Scenarios

### SimpleOS green channel wake contract

#### runs a channel wake through the scheduler-owned active pass

- Initialize the hosted SimpleOS SMP model with CPU two online
- smp init
- smp bringup ap
- Create a scheduler with one active green carrier
- var scheduler = Scheduler new with cpu count
- scheduler set green carrier parallelism
- Create carrier queues and park a green receiver on channel receive
- Send a value that wakes the parked receiver
- Run the scheduler-owned channel wake active pass
- Verify the wake pass enqueues work through the remote carrier
   - Expected: wake.apply.decision.target_cpu equals `2`
   - Expected: pending equals `smp_ipi_resched()`
   - Expected: wake.pass_result.rebalance.moved_workers equals `1`
   - Expected: wake.pass_result.ran_workers equals `1`
   - Expected: wake.reason equals `active_pass_ran`
- Verify the active pass moved execution back to the carrier CPU
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `504`
   - Expected: scheduler.green_current_task_on_cpu(2u32) equals `0`
   - Expected: green_carrier_queue_depth(wake.queues, 0) equals `0`
   - Expected: green_carrier_queue_depth(wake.queues, 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model with CPU two online")
smp_init()
smp_bringup_ap(2u32)
step("Create a scheduler with one active green carrier")
var scheduler = Scheduler.new_with_cpu_count(4u32)
scheduler.set_green_carrier_parallelism(1)
step("Create carrier queues and park a green receiver on channel receive")
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(504, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, parked_task.task_id)
step("Send a value that wakes the parked receiver")
val sent = green_channel_send(parked_recv.channel, 77)
step("Run the scheduler-owned channel wake active pass")
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

step("Verify the wake pass enqueues work through the remote carrier")
expect(sent.unparked).to_be(true)
expect(wake.enqueued).to_be(true)
expect(wake.apply.decision.target_cpu).to_equal(2)
expect(wake.apply.ipi_sent).to_be(true)
expect(pending).to_equal(smp_ipi_resched())
expect(wake.pass_result.rebalance.moved_workers).to_equal(1)
expect(wake.pass_result.ran_workers).to_equal(1)
expect(wake.ran).to_be(true)
expect(wake.reason).to_equal("active_pass_ran")
step("Verify the active pass moved execution back to the carrier CPU")
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(504)
expect(scheduler.green_current_task_on_cpu(2u32)).to_equal(0)
expect(green_carrier_queue_depth(wake.queues, 0)).to_equal(0)
expect(green_carrier_queue_depth(wake.queues, 2)).to_equal(0)
```

</details>

#### re-enqueues an unparked channel receiver through carrier dispatch

- Initialize the hosted SimpleOS SMP model with CPU two online
- smp init
- smp bringup ap
- Create scheduler state and carrier queues
- var scheduler = Scheduler new with cpu count
- Park a green task on channel receive
- Send a value that wakes the same parked task
- Create and apply the carrier wake decision
- Verify the receiver wake dispatches into green scheduler state
   - Expected: decision.target_cpu equals `2`
   - Expected: decision.reason equals `wake_affine_waker_cpu`
   - Expected: pending equals `smp_ipi_resched()`
   - Expected: green_carrier_queue_depth(applied.queues, 2) equals `1`
   - Expected: dispatched.task_id equals `501`
   - Expected: scheduler.green_current_task_on_cpu(2u32) equals `501`
   - Expected: scheduler.green_context_switches_on_cpu(2u32) equals `1`
   - Expected: scheduler.get_current_on_cpu(2u32).id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model with CPU two online")
smp_init()
smp_bringup_ap(2u32)
step("Create scheduler state and carrier queues")
var scheduler = Scheduler.new_with_cpu_count(4u32)
val queues = green_carrier_run_queues_new(4, 8)
step("Park a green task on channel receive")
val task = green_task_new(501, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, parked_task.task_id)
step("Send a value that wakes the same parked task")
val sent = green_channel_send(parked_recv.channel, 77)
step("Create and apply the carrier wake decision")
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

step("Verify the receiver wake dispatches into green scheduler state")
expect(sent.unparked).to_be(true)
expect(decision.should_enqueue).to_be(true)
expect(decision.target_cpu).to_equal(2)
expect(decision.reason).to_equal("wake_affine_waker_cpu")
expect(applied.enqueued).to_be(true)
expect(applied.ipi_sent).to_be(true)
expect(pending).to_equal(smp_ipi_resched())
expect(green_carrier_queue_depth(applied.queues, 2)).to_equal(1)
expect(dispatched.dispatched).to_be(true)
expect(dispatched.task_id).to_equal(501)
expect(scheduled.applied).to_be(true)
expect(scheduler.green_current_task_on_cpu(2u32)).to_equal(501)
expect(scheduler.green_context_switches_on_cpu(2u32)).to_equal(1)
expect(scheduler.get_current_on_cpu(2u32).id).to_equal(0)
```

</details>

#### does not enqueue when a send buffered without waking a receiver

- Initialize the hosted SimpleOS SMP model
- smp init
- Create carrier queues and a parked task without a matching channel receiver
- Send to a channel with no parked receiver
- Build and apply the no-receiver wake decision
- Verify no receiver wake is enqueued
   - Expected: decision.reason equals `channel_no_receiver`
   - Expected: applied.queues.queued_task_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create carrier queues and a parked task without a matching channel receiver")
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(502, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
step("Send to a channel with no parked receiver")
val sent = green_channel_send(green_channel_new(1), 88)
step("Build and apply the no-receiver wake decision")
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

step("Verify no receiver wake is enqueued")
expect(sent.unparked).to_be(false)
expect(decision.should_enqueue).to_be(false)
expect(decision.reason).to_equal("channel_no_receiver")
expect(applied.enqueued).to_be(false)
expect(applied.queues.queued_task_ids.len()).to_equal(0)
```

</details>

#### rejects mismatched channel wake task ids

- Initialize the hosted SimpleOS SMP model
- smp init
- Create carrier queues and park task 503
- Wake a different receiver task id
- Build and apply the mismatched wake decision
- Verify the mismatched receiver is rejected
   - Expected: sent.receiver_task_id equals `999`
   - Expected: decision.reason equals `channel_receiver_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create carrier queues and park task 503")
val queues = green_carrier_run_queues_new(4, 8)
val task = green_task_new(503, 4, 0, 0, 1, 2, 3)
val parked_task = green_task_park(task, "green_channel_recv")
step("Wake a different receiver task id")
val channel = green_channel_new(1)
val parked_recv = green_channel_recv(channel, 999)
val sent = green_channel_send(parked_recv.channel, 99)
step("Build and apply the mismatched wake decision")
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

step("Verify the mismatched receiver is rejected")
expect(sent.unparked).to_be(true)
expect(sent.receiver_task_id).to_equal(999)
expect(decision.should_enqueue).to_be(false)
expect(decision.reason).to_equal("channel_receiver_mismatch")
expect(applied.enqueued).to_be(false)
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
