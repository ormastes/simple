# Task Error Surfacing Specification

> <details>

<!-- sdn-diagram:id=task_error_surfacing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_error_surfacing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_error_surfacing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_error_surfacing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Error Surfacing Specification

## Scenarios

### HostScheduler death-reason API (W2-5 structural)

#### TaskDeathRecord struct exists with required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("struct TaskDeathRecord")).to_equal(true)
expect(src.contains("task_key: text")).to_equal(true)
expect(src.contains("task_id: usize")).to_equal(true)
expect(src.contains("reason: text")).to_equal(true)
```

</details>

#### HostScheduler has death_records field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("death_records: [TaskDeathRecord]")).to_equal(true)
```

</details>

#### HostTask has task_error field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("task_error: text")).to_equal(true)
```

</details>

#### last_death_reason accessor exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("fn last_death_reason() -> text")).to_equal(true)
```

</details>

#### death_count accessor exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("fn death_count() -> usize")).to_equal(true)
```

</details>

#### mark_task_error method exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("me mark_task_error(task_id: usize, error_text: text)")).to_equal(true)
```

</details>

#### death record is pushed on task completion with non-empty task_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("self.death_records = self.death_records.push(rec)")).to_equal(true)
```

</details>

#### current_unified_task_key stamps death records

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("current_unified_task_key")).to_equal(true)
```

</details>

#### run_result_task surfaces Err to handle (H3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = runtime_src()
expect(src.contains("me run_result_task<T>")).to_equal(true)
expect(src.contains("fn() -> Result<T, text>")).to_equal(true)
```

</details>

#### drain_result_errors populates AsyncError.JoinError

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = runtime_src()
expect(src.contains("AsyncError.JoinError")).to_equal(true)
expect(src.contains("me drain_result_errors<T>")).to_equal(true)
```

</details>

### HostScheduler death bookkeeping (W2-5 behavioural)

#### fresh scheduler has zero death_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = HostScheduler.new(1)
expect(sched.death_count()).to_equal(0)
```

</details>

#### last_death_reason on fresh scheduler is empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = HostScheduler.new(1)
val reason = sched.last_death_reason()
expect(reason).to_equal("")
```

</details>

#### death_records starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = HostScheduler.new(1)
expect(sched.death_records.is_empty()).to_equal(true)
```

</details>

#### mark_task_error on non-existent task is a no-op (no crash, no death record)

- var sched = HostScheduler new
- sched mark task error
   - Expected: sched.death_count() equals `0`
   - Expected: sched.last_death_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = HostScheduler.new(1)
sched.mark_task_error(999, "phantom-error")
expect(sched.death_count()).to_equal(0)
expect(sched.last_death_reason()).to_equal("")
```

</details>

### Task identity stamp for death reasons (W2-5 behavioural)

#### scheduler-task key is available while scheduler task is active

- exit scheduler task id
   - Expected: key equals `scheduler-task-101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = enter_scheduler_task_id(101)
val key = current_unified_task_key("fallback")
exit_scheduler_task_id(prev)
expect(key).to_equal("scheduler-task-101")
```

</details>

#### current_scheduler_task_key returns fallback when no task active

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = current_scheduler_task_key("no-active-task")
expect(key).to_equal("no-active-task")
```

</details>

#### death reason key matches the task id entered

- exit scheduler task id
   - Expected: key equals `scheduler-task-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = enter_scheduler_task_id(42)
val key = current_unified_task_key("ignored-fallback")
exit_scheduler_task_id(prev)
expect(key).to_equal("scheduler-task-42")
```

</details>

#### sibling task identity not affected after first task exits

- exit scheduler task id
- exit scheduler task id
   - Expected: key equals `scheduler-task-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev_a = enter_scheduler_task_id(1)
exit_scheduler_task_id(prev_a)
val prev_b = enter_scheduler_task_id(2)
val key = current_unified_task_key("fb")
exit_scheduler_task_id(prev_b)
# sibling task B completed; its key was scheduler-task-2
expect(key).to_equal("scheduler-task-2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HostScheduler death-reason API (W2-5 structural)
- HostScheduler death bookkeeping (W2-5 behavioural)
- Task identity stamp for death reasons (W2-5 behavioural)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
