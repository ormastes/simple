# SimpleOS Multicore Green System Contract

> This system spec exercises the hosted SimpleOS contract for multicore green work: logical green tasks enqueue onto carrier CPUs, remote enqueue uses the SMP reschedule IPI surface, and the real `Scheduler` records green execution state separately from normal OS task ids.

<!-- sdn-diagram:id=simpleos_multicore_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_multicore_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_multicore_green_spec -> std
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Multicore Green System Contract

This system spec exercises the hosted SimpleOS contract for multicore green work: logical green tasks enqueue onto carrier CPUs, remote enqueue uses the SMP reschedule IPI surface, and the real `Scheduler` records green execution state separately from normal OS task ids.

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
separately from normal OS task ids.

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

## Scenarios

### SimpleOS multicore green contract

#### routes remote green enqueue through the SimpleOS reschedule IPI surface

1. smp init

2. smp bringup ap
   - Expected: result.enqueued is true
   - Expected: result.ipi_sent is true
   - Expected: result.ipi_reason_mask equals `smp_ipi_resched()`
   - Expected: smp_take_ipi(1u32) equals `smp_ipi_resched()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(1u32)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(101, 4, 0, 3, 1, 2, 4, 0)
val result = green_carrier_apply_enqueue(queues, decision)

expect(result.enqueued).to_equal(true)
expect(result.ipi_sent).to_equal(true)
expect(result.ipi_reason_mask).to_equal(smp_ipi_resched())
expect(smp_take_ipi(1u32)).to_equal(smp_ipi_resched())
```

</details>

#### dispatches green work into scheduler-owned multicore execution state

1. smp init

2. smp bringup ap

3. var scheduler = Scheduler new with cpu count
   - Expected: applied.applied is true
   - Expected: scheduler.green_current_task_on_cpu(1u32) equals `202`
   - Expected: scheduler.green_context_switches_on_cpu(1u32) equals `1`
   - Expected: scheduler.green_rejected_intents() equals `0`
   - Expected: scheduler.get_current_on_cpu(1u32).id equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
smp_bringup_ap(1u32)
var scheduler = Scheduler.new_with_cpu_count(4u32)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(202, 4, 0, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
val applied = scheduler.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(applied.applied).to_equal(true)
expect(scheduler.green_current_task_on_cpu(1u32)).to_equal(202)
expect(scheduler.green_context_switches_on_cpu(1u32)).to_equal(1)
expect(scheduler.green_rejected_intents()).to_equal(0)
expect(scheduler.get_current_on_cpu(1u32).id).to_equal(0)
```

</details>

#### extends green scheduler slots when SimpleOS topology grows

1. smp init

2. var scheduler = Scheduler new bootstrap

3. scheduler set topology
   - Expected: applied.applied is true
   - Expected: scheduler.green_current_task_on_cpu(3u32) equals `303`
   - Expected: scheduler.green_context_switches_on_cpu(3u32) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smp_init()
var scheduler = Scheduler.new_bootstrap()
scheduler.set_topology(default_scheduler_topology(4u32))
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(303, 4, 8, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 3)
val applied = scheduler.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))

expect(applied.applied).to_equal(true)
expect(scheduler.green_current_task_on_cpu(3u32)).to_equal(303)
expect(scheduler.green_context_switches_on_cpu(3u32)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
