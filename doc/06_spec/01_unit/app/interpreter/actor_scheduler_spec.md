# Actor Scheduler Specification

> <details>

<!-- sdn-diagram:id=actor_scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_scheduler_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Scheduler Specification

## Scenarios

### Actor Scheduler

#### keeps actor priority state and scheduler config available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = actor_scheduler_source()

expect(source).to_contain("enum ActorPriority:")
expect(source).to_contain("static fn from_i64(i: i64) -> ActorPriority")
expect(source).to_contain("static fn to_i64(p: ActorPriority) -> i64")
expect(source).to_contain("enum ActorState:")
expect(source).to_contain("class SchedulerConfig:")
expect(source).to_contain("static fn default() -> SchedulerConfig")
```

</details>

#### keeps run queue actor context and scheduler operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = actor_scheduler_source()

expect(source).to_contain("class RunQueue:")
expect(source).to_contain("me enqueue(actor_id: i64, priority: ActorPriority)")
expect(source).to_contain("me dequeue()")
expect(source).to_contain("class ActorContext:")
expect(source).to_contain("class ActorScheduler:")
expect(source).to_contain("me spawn_actor(name) -> i64")
expect(source).to_contain("me run_one_timeslice() -> bool")
expect(source).to_contain("me send_message(id: i64, data_ref: i64, size: i64, sender) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/actor_scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Actor Scheduler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
