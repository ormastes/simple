# Scheduler Specification

> <details>

<!-- sdn-diagram:id=scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Specification

## Scenarios

### Scheduler

#### defines fixed-slot task state and scheduler construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/scheduler.spl")

expect(scheduler).to_contain("val MAX_TASKS: i32 = 16")
expect(scheduler).to_contain("class TaskSlot:")
expect(scheduler).to_contain("task_fn: i64")
expect(scheduler).to_contain("is_active: bool")
expect(scheduler).to_contain("is_complete: bool")
expect(scheduler).to_contain("priority: i32")
expect(scheduler).to_contain("class NoallocScheduler:")
expect(scheduler).to_contain("tasks: [TaskSlot]")
expect(scheduler).to_contain("completed_mask: i64")
expect(scheduler).to_contain("static fn new() -> NoallocScheduler:")
```

</details>

#### defines spawn, completion, cancellation, and query lifecycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/scheduler.spl")
val init = rt_file_read_text("src/lib/nogc_async_mut_noalloc/async/__init__.spl")

expect(scheduler).to_contain("me spawn(task_fn: i64, priority: i32) -> i32:")
expect(scheduler).to_contain("return i")
expect(scheduler).to_contain("-1")
expect(scheduler).to_contain("me complete_task(task_id: i32, value: i64):")
expect(scheduler).to_contain("self.completed_mask = self.completed_mask | (bit << task_id)")
expect(scheduler).to_contain("me cancel(task_id: i32):")
expect(scheduler).to_contain("fn is_task_complete(task_id: i32) -> bool:")
expect(scheduler).to_contain("fn task_result(task_id: i32) -> i64:")
expect(scheduler).to_contain("fn is_idle() -> bool:")
expect(scheduler).to_contain("self.active_count == 0")
expect(init).to_contain("export MAX_TASKS, TaskSlot, NoallocScheduler")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/async/scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Scheduler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
