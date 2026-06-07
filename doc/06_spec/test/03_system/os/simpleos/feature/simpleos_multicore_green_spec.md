# SimpleOS Multicore Green System Contract

> This system spec exercises the hosted SimpleOS contract for multicore green work: logical green tasks enqueue onto carrier CPUs, remote enqueue uses the SMP reschedule IPI surface, and the real `Scheduler` records green execution state separately from normal OS task ids. It also proves the hosted SimpleOS lane routes runtime, timer, and compiler preemption safepoints through named scheduler-owned green carrier adapters.

<!-- sdn-diagram:id=simpleos_multicore_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_multicore_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_multicore_green_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_multicore_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Multicore Green System Contract

This system spec exercises the hosted SimpleOS contract for multicore green work: logical green tasks enqueue onto carrier CPUs, remote enqueue uses the SMP reschedule IPI surface, and the real `Scheduler` records green execution state separately from normal OS task ids. It also proves the hosted SimpleOS lane routes runtime, timer, and compiler preemption safepoints through named scheduler-owned green carrier adapters.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-multicore |
| Category | SimpleOS / Concurrency |
| Status | In Progress |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec exercises the hosted SimpleOS contract for multicore green
work: logical green tasks enqueue onto carrier CPUs, remote enqueue uses the SMP
reschedule IPI surface, and the real `Scheduler` records green execution state
separately from normal OS task ids. It also proves the hosted SimpleOS lane
routes runtime, timer, and compiler preemption safepoints through named
scheduler-owned green carrier adapters.

The spec is intentionally not a live QEMU proof. The QEMU SMP evidence remains
tracked in the multicore-green system plan until guest-visible AP execution is
available to assert.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the hosted SimpleOS multicore-green contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter --clean
```

## Examples

The scenarios model the SimpleOS scheduler-owned carrier path: remote green
enqueue sends the reschedule IPI, dispatch records green execution separately
from normal OS tasks, topology growth extends green scheduler slots, and
runtime, timer, and compiler safepoints route through active green carriers.
This is hosted model evidence; live QEMU/AP execution remains covered by
`test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`.

## Scenario Walkthrough

### Remote Green Enqueue

- Initialize the hosted SMP model.
- Bring up a remote application processor.
- Create carrier queues for four CPUs.
- Plan green work for a remote carrier CPU.
- Apply the enqueue decision.
- Assert the enqueue sent the SimpleOS reschedule IPI.

### Scheduler-Owned Green State

- Create a scheduler with four CPU slots.
- Enqueue green work for CPU one.
- Dispatch the next green task from the CPU one carrier queue.
- Apply the green scheduler intent.
- Assert green current-task and green context-switch counters changed.
- Assert the normal OS task slot remains unchanged.

### Topology Growth

- Create a bootstrap scheduler.
- Grow the topology to four CPUs.
- Enqueue green work for CPU three.
- Dispatch and apply CPU three green scheduler intent.
- Assert the grown scheduler records CPU three green execution.

### Active-Carrier Safepoints

- Set active green carrier parallelism to one.
- Enqueue and run green work on CPU zero.
- Poll the named runtime safepoint adapter through active green carriers.
- Poll the named timer interrupt adapter through active green carriers.
- Poll the named compiler safepoint adapter through active green carriers.
- Assert runtime and first compiler polling ticks without preemption.
- Assert timer and second compiler polling yield and requeue the active green
  worker.
- Poll an invalid source and assert no carrier is ticked or yielded.

## Evidence Boundary

- This spec proves hosted/model SimpleOS scheduler behavior.
- It proves scheduler-owned carrier state, remote enqueue/IPI intent,
  topology-bounded green state, and named preemption-safepoint routing.
- It does not by itself prove live AP hardware execution.
- Live AP and guest-visible dispatch evidence is owned by
  `green_carrier_qemu_spec.spl`.
- Final hardware context-switch handoff remains tracked until live guest proof
  covers that exact transition.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl
[1/1] test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl PASSED
Files: 1
Passed: 6
Failed: 0
```

## Scenarios

### SimpleOS multicore green contract

#### routes remote green enqueue through the SimpleOS reschedule IPI surface

- Initialize the hosted SimpleOS SMP model
- smp init
- Bring up a remote application processor
- smp bringup ap
- Create carrier run queues for four CPUs
- Plan a green task for a remote carrier CPU
- Apply the enqueue decision through the SimpleOS carrier queues
- Verify remote enqueue sends the SimpleOS reschedule IPI
   - Expected: result.enqueued is true
   - Expected: result.ipi_sent is true
   - Expected: result.ipi_reason_mask equals `smp_ipi_resched()`
   - Expected: smp_take_ipi(1u32) equals `smp_ipi_resched()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Bring up a remote application processor")
smp_bringup_ap(1u32)
step("Create carrier run queues for four CPUs")
val queues = green_carrier_run_queues_new(4, 8)
step("Plan a green task for a remote carrier CPU")
val decision = green_carrier_spawn_task(101, 4, 0, 3, 1, 2, 4, 0)
step("Apply the enqueue decision through the SimpleOS carrier queues")
val result = green_carrier_apply_enqueue(queues, decision)

step("Verify remote enqueue sends the SimpleOS reschedule IPI")
expect(result.enqueued).to_equal(true)
expect(result.ipi_sent).to_equal(true)
expect(result.ipi_reason_mask).to_equal(smp_ipi_resched())
expect(smp_take_ipi(1u32)).to_equal(smp_ipi_resched())
```

</details>

#### dispatches green work into scheduler-owned multicore execution state

- Initialize the hosted SimpleOS SMP model
- smp init
- Bring up a remote application processor
- smp bringup ap
- Create a scheduler with four CPU slots
- var scheduler = Scheduler new with cpu count
- Create carrier queues and enqueue green work for CPU one
- Dispatch the next green task from CPU one carrier queue
- Apply the dispatched green scheduler intent
- Verify green execution state is separate from the normal task slot
   - Expected: applied.applied is true
   - Expected: scheduler.green_current_task_on_cpu(1u32) equals `202`
   - Expected: scheduler.green_context_switches_on_cpu(1u32) equals `1`
   - Expected: scheduler.green_rejected_intents() equals `0`
   - Expected: scheduler.get_current_on_cpu(1u32).id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Bring up a remote application processor")
smp_bringup_ap(1u32)
step("Create a scheduler with four CPU slots")
var scheduler = Scheduler.new_with_cpu_count(4u32)
step("Create carrier queues and enqueue green work for CPU one")
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(202, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
step("Dispatch the next green task from CPU one carrier queue")
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
step("Apply the dispatched green scheduler intent")
val applied = scheduler.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

step("Verify green execution state is separate from the normal task slot")
expect(applied.applied).to_equal(true)
expect(scheduler.green_current_task_on_cpu(1u32)).to_equal(202)
expect(scheduler.green_context_switches_on_cpu(1u32)).to_equal(1)
expect(scheduler.green_rejected_intents()).to_equal(0)
expect(scheduler.get_current_on_cpu(1u32).id).to_equal(0)
```

</details>

#### extends green scheduler slots when SimpleOS topology grows

- Initialize the hosted SimpleOS SMP model
- smp init
- Create a bootstrap scheduler and grow it to four CPUs
- var scheduler = Scheduler new bootstrap
- scheduler set topology
- Create carrier queues and enqueue green work for CPU three
- Dispatch and apply the CPU three green scheduler intent
- Verify the grown scheduler records CPU three green execution
   - Expected: applied.applied is true
   - Expected: scheduler.green_current_task_on_cpu(3u32) equals `303`
   - Expected: scheduler.green_context_switches_on_cpu(3u32) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create a bootstrap scheduler and grow it to four CPUs")
var scheduler = Scheduler.new_bootstrap()
scheduler.set_topology(default_scheduler_topology(4u32))
step("Create carrier queues and enqueue green work for CPU three")
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(303, 4, 8, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
step("Dispatch and apply the CPU three green scheduler intent")
val dispatched = green_carrier_dispatch_next(queued.queues, 3)
val applied = scheduler.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

step("Verify the grown scheduler records CPU three green execution")
expect(applied.applied).to_equal(true)
expect(scheduler.green_current_task_on_cpu(3u32)).to_equal(303)
expect(scheduler.green_context_switches_on_cpu(3u32)).to_equal(1)
```

</details>

#### routes SimpleOS preemption safepoints through active green carriers

- Initialize the hosted SimpleOS SMP model
- smp init
- Create a scheduler with one active green carrier
- var scheduler = Scheduler new with cpu count
- scheduler set green carrier parallelism
- Enqueue green work on CPU zero
- Run an active carrier pass
- Poll the named runtime safepoint adapter through active green carriers
- Poll the named timer interrupt adapter through active green carriers
- Verify runtime safepoint ticks without requesting preemption
   - Expected: pass_result.ran_workers equals `1`
   - Expected: runtime_poll.accepted is true
   - Expected: runtime_poll.source equals `runtime_safepoint`
   - Expected: runtime_poll.preemption_requested is false
   - Expected: runtime_poll.ticked_carriers equals `1`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `404`
- Verify timer safepoint yields the active green worker
   - Expected: timer_interrupt.accepted is true
   - Expected: timer_interrupt.source equals `timer_interrupt`
   - Expected: timer_interrupt.preemption.preemption_requested is true
   - Expected: timer_interrupt.eoi_required is true
   - Expected: timer_interrupt.yielded_workers equals `1`
   - Expected: timer_interrupt.reason equals `green_time_slice_expired`
   - Expected: green_carrier_queue_depth(timer_interrupt.queues, 0) equals `1`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create a scheduler with one active green carrier")
var scheduler = Scheduler.new_with_cpu_count(4u32)
scheduler.set_green_carrier_parallelism(1)
step("Enqueue green work on CPU zero")
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(404, 4, 1, 0, 4, 4, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
step("Run an active carrier pass")
val pass_result = scheduler.run_green_carrier_active_pass(queued.queues, 0)
step("Poll the named runtime safepoint adapter through active green carriers")
val runtime_poll = scheduler.green_runtime_safepoint_active_carriers(pass_result.queues)
step("Poll the named timer interrupt adapter through active green carriers")
val timer_interrupt = scheduler.green_timer_interrupt_active_carriers(runtime_poll.queues)

step("Verify runtime safepoint ticks without requesting preemption")
expect(pass_result.ran_workers).to_equal(1)
expect(runtime_poll.accepted).to_equal(true)
expect(runtime_poll.source).to_equal("runtime_safepoint")
expect(runtime_poll.preemption_requested).to_equal(false)
expect(runtime_poll.ticked_carriers).to_equal(1)
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(404)
step("Verify timer safepoint yields the active green worker")
expect(timer_interrupt.accepted).to_equal(true)
expect(timer_interrupt.source).to_equal("timer_interrupt")
expect(timer_interrupt.preemption.preemption_requested).to_equal(true)
expect(timer_interrupt.eoi_required).to_equal(true)
expect(timer_interrupt.yielded_workers).to_equal(1)
expect(timer_interrupt.reason).to_equal("green_time_slice_expired")
expect(green_carrier_queue_depth(timer_interrupt.queues, 0)).to_equal(1)
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(0)
```

</details>

#### routes compiler safepoints through the named SimpleOS green adapter

- Initialize the hosted SimpleOS SMP model
- smp init
- Create a scheduler with one active green carrier
- var scheduler = Scheduler new with cpu count
- scheduler set green carrier parallelism
- Enqueue compiler-yieldable green work on CPU zero
- Run an active carrier pass
- Poll the compiler safepoint before the time slice expires
- Poll the compiler safepoint at time-slice expiry
- Verify the compiler safepoint adapter preserves the running worker before expiry
   - Expected: pass_result.ran_workers equals `1`
   - Expected: compiler_running_poll.accepted is true
   - Expected: compiler_running_poll.source equals `compiler_safepoint`
   - Expected: compiler_running_poll.preemption_requested is false
   - Expected: compiler_running_poll.ticked_carriers equals `1`
   - Expected: compiler_running_poll.yielded_workers equals `0`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `406`
- Verify the compiler safepoint adapter yields at time-slice expiry
   - Expected: compiler_expiring_poll.accepted is true
   - Expected: compiler_expiring_poll.source equals `compiler_safepoint`
   - Expected: compiler_expiring_poll.preemption_requested is true
   - Expected: compiler_expiring_poll.yielded_workers equals `1`
   - Expected: compiler_expiring_poll.reason equals `green_time_slice_expired`
   - Expected: green_carrier_queue_depth(compiler_expiring_poll.queues, 0) equals `1`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create a scheduler with one active green carrier")
var scheduler = Scheduler.new_with_cpu_count(4u32)
scheduler.set_green_carrier_parallelism(1)
step("Enqueue compiler-yieldable green work on CPU zero")
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(406, 4, 1, 0, 4, 4, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
step("Run an active carrier pass")
val pass_result = scheduler.run_green_carrier_active_pass(queued.queues, 0)
step("Poll the compiler safepoint before the time slice expires")
val compiler_running_poll = scheduler.green_compiler_safepoint_active_carriers(pass_result.queues)
step("Poll the compiler safepoint at time-slice expiry")
val compiler_expiring_poll = scheduler.green_compiler_safepoint_active_carriers(compiler_running_poll.queues)

step("Verify the compiler safepoint adapter preserves the running worker before expiry")
expect(pass_result.ran_workers).to_equal(1)
expect(compiler_running_poll.accepted).to_equal(true)
expect(compiler_running_poll.source).to_equal("compiler_safepoint")
expect(compiler_running_poll.preemption_requested).to_equal(false)
expect(compiler_running_poll.ticked_carriers).to_equal(1)
expect(compiler_running_poll.yielded_workers).to_equal(0)
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(406)
step("Verify the compiler safepoint adapter yields at time-slice expiry")
expect(compiler_expiring_poll.accepted).to_equal(true)
expect(compiler_expiring_poll.source).to_equal("compiler_safepoint")
expect(compiler_expiring_poll.preemption_requested).to_equal(true)
expect(compiler_expiring_poll.yielded_workers).to_equal(1)
expect(compiler_expiring_poll.reason).to_equal("green_time_slice_expired")
expect(green_carrier_queue_depth(compiler_expiring_poll.queues, 0)).to_equal(1)
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(0)
```

</details>

#### rejects bad SimpleOS preemption source without ticking carriers

- Initialize the hosted SimpleOS SMP model
- smp init
- Create a scheduler with one active green carrier
- var scheduler = Scheduler new with cpu count
- scheduler set green carrier parallelism
- Enqueue green work on CPU zero
- Run an active carrier pass
- Poll an invalid SimpleOS preemption source
- Verify the invalid safepoint does not tick or yield carriers
   - Expected: rejected.accepted is false
   - Expected: rejected.reason equals `invalid_preemption_source`
   - Expected: rejected.ticked_carriers equals `0`
   - Expected: rejected.yielded_workers equals `0`
   - Expected: green_carrier_queue_depth(rejected.queues, 0) equals `0`
   - Expected: scheduler.green_current_task_on_cpu(0u32) equals `405`
   - Expected: scheduler.green_ticks_remaining_on_cpu(0u32) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize the hosted SimpleOS SMP model")
smp_init()
step("Create a scheduler with one active green carrier")
var scheduler = Scheduler.new_with_cpu_count(4u32)
scheduler.set_green_carrier_parallelism(1)
step("Enqueue green work on CPU zero")
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(405, 4, 1, 0, 4, 4, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
step("Run an active carrier pass")
val pass_result = scheduler.run_green_carrier_active_pass(queued.queues, 0)
step("Poll an invalid SimpleOS preemption source")
val rejected = scheduler.green_preemption_safepoint_active_carriers(pass_result.queues, "bad_simpleos_source")

step("Verify the invalid safepoint does not tick or yield carriers")
expect(rejected.accepted).to_equal(false)
expect(rejected.reason).to_equal("invalid_preemption_source")
expect(rejected.ticked_carriers).to_equal(0)
expect(rejected.yielded_workers).to_equal(0)
expect(green_carrier_queue_depth(rejected.queues, 0)).to_equal(0)
expect(scheduler.green_current_task_on_cpu(0u32)).to_equal(405)
expect(scheduler.green_ticks_remaining_on_cpu(0u32)).to_equal(2)
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


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
