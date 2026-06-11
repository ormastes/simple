# Executor & Scheduler Intensive Tests

> Intensive tests for the single-threaded Executor, priority-based Scheduler, Task lifecycle, and Runtime global functions.

<!-- sdn-diagram:id=executor_scheduler_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=executor_scheduler_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

executor_scheduler_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=executor_scheduler_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executor & Scheduler Intensive Tests

Intensive tests for the single-threaded Executor, priority-based Scheduler, Task lifecycle, and Runtime global functions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/executor_scheduler_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for the single-threaded Executor, priority-based Scheduler,
Task lifecycle, and Runtime global functions.

## Scenarios

### Task Creation

#### creates a task with default priority 0

1. var task = Task new
   - Expected: task.priority equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_42)
expect(task.priority).to_equal(0)
```

</details>

#### creates a task in Pending state

1. var task = Task new
   - Expected: task.state == TaskState.Pending is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_42)
expect(task.state == TaskState.Pending).to_equal(true)
```

</details>

#### creates a task with specified priority

1. var task = Task with priority
   - Expected: task.priority equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.with_priority(poll_returns_42, 5)
expect(task.priority).to_equal(5)
```

</details>

#### assigns unique IDs to each task

1. var t1 = Task new
2. var t2 = Task new
   - Expected: t2.id > t1.id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var id_before = global_task_id
var t1 = Task.new(poll_returns_42)
var t2 = Task.new(poll_returns_100)
expect(t2.id > t1.id).to_equal(true)
```

</details>

### Task State Transitions

#### transitions from Pending to Completed on successful execute

1. var task = Task new
   - Expected: task.state == TaskState.Pending is true
2. task execute
   - Expected: task.state == TaskState.Completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_42)
expect(task.state == TaskState.Pending).to_equal(true)
task.execute()
expect(task.state == TaskState.Completed).to_equal(true)
```

</details>

#### stores the result after execution

1. var task = Task new
2. task execute
   - Expected: task.result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_42)
task.execute()
expect(task.result).to_equal(42)
```

</details>

#### transitions to Failed when poll returns negative

1. var task = Task new
2. task execute
   - Expected: task.state == TaskState.Failed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_negative)
task.execute()
expect(task.state == TaskState.Failed).to_equal(true)
```

</details>

#### reports is_complete correctly

1. var task = Task new
   - Expected: task.is_complete() is false
2. task execute
   - Expected: task.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_100)
expect(task.is_complete()).to_equal(false)
task.execute()
expect(task.is_complete()).to_equal(true)
```

</details>

#### reports is_failed correctly

1. var task = Task new
   - Expected: task.is_failed() is false
2. task execute
   - Expected: task.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_negative)
expect(task.is_failed()).to_equal(false)
task.execute()
expect(task.is_failed()).to_equal(true)
```

</details>

### Executor Basics

#### creates an empty executor

1. var exec = Executor new
   - Expected: exec.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
expect(exec.task_count()).to_equal(0)
```

</details>

#### is idle when no tasks are spawned

1. var exec = Executor new
   - Expected: exec.is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
expect(exec.is_idle()).to_equal(true)
```

</details>

#### tracks task count after spawn

1. var exec = Executor new
2. var t1 = Task new
3. exec spawn
   - Expected: exec.task_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var t1 = Task.new(poll_returns_42)
exec.spawn(t1)
expect(exec.task_count()).to_equal(1)
```

</details>

#### is not idle after spawning a task

1. var exec = Executor new
2. exec spawn
   - Expected: exec.is_idle() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
exec.spawn(Task.new(poll_returns_42))
expect(exec.is_idle()).to_equal(false)
```

</details>

### Executor Run

#### runs with no tasks without error

1. var exec = Executor new
2. exec run
   - Expected: exec.completed_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
exec.run()
expect(exec.completed_count()).to_equal(0)
```

</details>

#### executes a single task to completion

1. var exec = Executor new
2. var task = Task new
3. exec spawn
4. exec run
   - Expected: finished.is_complete() is true
   - Expected: finished.result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var task = Task.new(poll_returns_42)
exec.spawn(task)
exec.run()
var finished = exec.tasks[0]
expect(finished.is_complete()).to_equal(true)
expect(finished.result).to_equal(42)
```

</details>

#### executes multiple tasks and completes all

1. var exec = Executor new
2. var t1 = Task new
3. var t2 = Task new
4. var t3 = Task new
5. exec spawn
6. exec spawn
7. exec spawn
8. exec run
   - Expected: exec.completed_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var t1 = Task.new(poll_returns_42)
var t2 = Task.new(poll_returns_100)
var t3 = Task.new(poll_returns_7)
exec.spawn(t1)
exec.spawn(t2)
exec.spawn(t3)
exec.run()
expect(exec.completed_count()).to_equal(3)
```

</details>

#### tracks completed count correctly

1. var exec = Executor new
2. exec spawn
3. exec spawn
4. exec run
   - Expected: exec.completed_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
exec.spawn(Task.new(poll_returns_42))
exec.spawn(Task.new(poll_returns_100))
exec.run()
expect(exec.completed_count()).to_equal(2)
```

</details>

### Executor Run One

#### returns false when no tasks exist

1. var exec = Executor new
2. var found = exec run one
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var found = exec.run_one()
expect(found).to_equal(false)
```

</details>

#### processes exactly one pending task

1. var exec = Executor new
2. var t1 = Task new
3. var t2 = Task new
4. exec spawn
5. exec spawn
6. var found = exec run one
   - Expected: found is true
   - Expected: first.is_complete() is true
   - Expected: second.state == TaskState.Pending is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var t1 = Task.new(poll_returns_42)
var t2 = Task.new(poll_returns_100)
exec.spawn(t1)
exec.spawn(t2)
var found = exec.run_one()
expect(found).to_equal(true)
var first = exec.tasks[0]
var second = exec.tasks[1]
expect(first.is_complete()).to_equal(true)
expect(second.state == TaskState.Pending).to_equal(true)
```

</details>

#### returns false after all tasks are completed

1. var exec = Executor new
2. exec spawn
3. exec run
4. var found = exec run one
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
exec.spawn(Task.new(poll_returns_42))
exec.run()
var found = exec.run_one()
expect(found).to_equal(false)
```

</details>

### Executor Block On

#### blocks and returns the task result

1. var exec = Executor new
2. var result = exec block on
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var result = exec.block_on(poll_returns_42)
expect(result).to_equal(42)
```

</details>

#### blocks on a computation and returns correct value

1. var exec = Executor new
2. var result = exec block on
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var result = exec.block_on(poll_adds_10_20)
expect(result).to_equal(30)
```

</details>

### Scheduler Priority

#### runs high priority tasks before normal

1. var sched = Scheduler new
2. var high task = Task with priority
3. var normal task = Task with priority
4. sched schedule
5. sched schedule
6. sched run
   - Expected: sched.run_order[0] equals `high_task.id`
   - Expected: sched.run_order[1] equals `normal_task.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var high_task = Task.with_priority(poll_returns_1, 1)
var normal_task = Task.with_priority(poll_returns_99, 0)
sched.schedule(high_task)
sched.schedule(normal_task)
sched.run()
# high_task id should appear before normal_task id in run_order
expect(sched.run_order[0]).to_equal(high_task.id)
expect(sched.run_order[1]).to_equal(normal_task.id)
```

</details>

#### runs normal priority tasks before low

1. var sched = Scheduler new
2. var normal task = Task with priority
3. var low task = Task with priority
4. sched schedule
5. sched schedule
6. sched run
   - Expected: sched.run_order[0] equals `normal_task.id`
   - Expected: sched.run_order[1] equals `low_task.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var normal_task = Task.with_priority(poll_returns_5, 0)
var low_task = Task.with_priority(poll_returns_1, -1)
sched.schedule(normal_task)
sched.schedule(low_task)
sched.run()
expect(sched.run_order[0]).to_equal(normal_task.id)
expect(sched.run_order[1]).to_equal(low_task.id)
```

</details>

#### runs all three priority levels in correct order

1. var sched = Scheduler new
2. var low task = Task with priority
3. var high task = Task with priority
4. var normal task = Task with priority
5. sched schedule
6. sched schedule
7. sched schedule
8. sched run
   - Expected: sched.run_order[0] equals `high_task.id`
   - Expected: sched.run_order[1] equals `normal_task.id`
   - Expected: sched.run_order[2] equals `low_task.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var low_task = Task.with_priority(poll_returns_1, -1)
var high_task = Task.with_priority(poll_returns_200, 2)
var normal_task = Task.with_priority(poll_returns_5, 0)
# Schedule in reverse order to prove ordering works
sched.schedule(low_task)
sched.schedule(normal_task)
sched.schedule(high_task)
sched.run()
expect(sched.run_order[0]).to_equal(high_task.id)
expect(sched.run_order[1]).to_equal(normal_task.id)
expect(sched.run_order[2]).to_equal(low_task.id)
```

</details>

### Scheduler Mixed

#### handles multiple tasks at each priority level

1. var sched = Scheduler new
2. var h1 = Task with priority
3. var h2 = Task with priority
4. var n1 = Task with priority
5. var l1 = Task with priority
6. var l2 = Task with priority
7. sched schedule
8. sched schedule
9. sched schedule
10. sched schedule
11. sched schedule
12. sched run
   - Expected: sched.run_order.length() equals `5`
   - Expected: sched.run_order[0] equals `h1.id`
   - Expected: sched.run_order[1] equals `h2.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var h1 = Task.with_priority(poll_returns_1, 1)
var h2 = Task.with_priority(poll_returns_5, 3)
var n1 = Task.with_priority(poll_returns_42, 0)
var l1 = Task.with_priority(poll_returns_7, -1)
var l2 = Task.with_priority(poll_returns_99, -2)
sched.schedule(l1)
sched.schedule(h1)
sched.schedule(n1)
sched.schedule(l2)
sched.schedule(h2)
sched.run()
# All 5 tasks should have run
expect(sched.run_order.length()).to_equal(5)
# First two should be h1 and h2 (high priority)
expect(sched.run_order[0]).to_equal(h1.id)
expect(sched.run_order[1]).to_equal(h2.id)
```

</details>

#### completes all scheduled tasks eventually

1. var sched = Scheduler new
2. sched schedule
3. sched schedule
4. sched schedule
5. sched run
   - Expected: sched.has_runnable() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
sched.schedule(Task.with_priority(poll_returns_42, 1))
sched.schedule(Task.with_priority(poll_returns_100, 0))
sched.schedule(Task.with_priority(poll_returns_7, -1))
sched.run()
expect(sched.has_runnable()).to_equal(false)
```

</details>

### Scheduler Empty

#### runs on empty scheduler without error

1. var sched = Scheduler new
2. sched run
   - Expected: sched.total_tasks() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
sched.run()
expect(sched.total_tasks()).to_equal(0)
```

</details>

#### has no runnable tasks when empty

1. var sched = Scheduler new
   - Expected: sched.has_runnable() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
expect(sched.has_runnable()).to_equal(false)
```

</details>

### Runtime Global IDs

#### increments global task IDs

1. var id1 = next task id
2. var id2 = next task id
   - Expected: id2 equals `id1 + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var id1 = next_task_id()
var id2 = next_task_id()
expect(id2).to_equal(id1 + 1)
```

</details>

#### produces unique IDs across tasks

1. var t1 = Task new
2. var t2 = Task new
3. var t3 = Task new
   - Expected: t1.id != t2.id is true
   - Expected: t2.id != t3.id is true
   - Expected: t1.id != t3.id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t1 = Task.new(poll_returns_42)
var t2 = Task.new(poll_returns_100)
var t3 = Task.new(poll_returns_7)
expect(t1.id != t2.id).to_equal(true)
expect(t2.id != t3.id).to_equal(true)
expect(t1.id != t3.id).to_equal(true)
```

</details>

### Edge Cases

#### handles zero-result tasks correctly

1. var task = Task new
2. task execute
   - Expected: task.is_complete() is true
   - Expected: task.result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task.new(poll_returns_0)
task.execute()
expect(task.is_complete()).to_equal(true)
expect(task.result).to_equal(0)
```

</details>

#### handles negative priority tasks in scheduler

1. var sched = Scheduler new
2. var task = Task with priority
3. sched schedule
   - Expected: sched.low.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var task = Task.with_priority(poll_returns_42, -5)
sched.schedule(task)
expect(sched.low.length()).to_equal(1)
```

</details>

#### handles very high priority tasks in scheduler

1. var sched = Scheduler new
2. var task = Task with priority
3. sched schedule
   - Expected: sched.high.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
var task = Task.with_priority(poll_returns_42, 999)
sched.schedule(task)
expect(sched.high.length()).to_equal(1)
```

</details>

#### executor handles mix of successful and failed tasks

1. var exec = Executor new
2. var good = Task new
3. var bad = Task new
4. exec spawn
5. exec spawn
6. exec run
   - Expected: good_result.is_complete() is true
   - Expected: bad_result.is_failed() is true
   - Expected: exec.completed_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var good = Task.new(poll_returns_42)
var bad = Task.new(poll_returns_negative)
exec.spawn(good)
exec.spawn(bad)
exec.run()
var good_result = exec.tasks[0]
var bad_result = exec.tasks[1]
expect(good_result.is_complete()).to_equal(true)
expect(bad_result.is_failed()).to_equal(true)
# Only successful tasks count as completed
expect(exec.completed_count()).to_equal(1)
```

</details>

#### scheduler total_tasks counts all priorities

1. var sched = Scheduler new
2. sched schedule
3. sched schedule
4. sched schedule
   - Expected: sched.total_tasks() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
sched.schedule(Task.with_priority(poll_returns_1, 1))
sched.schedule(Task.with_priority(poll_returns_5, 0))
sched.schedule(Task.with_priority(poll_returns_7, -1))
expect(sched.total_tasks()).to_equal(3)
```

</details>

#### block_on with multiply computation

1. var exec = Executor new
2. var result = exec block on
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exec = Executor.new()
var result = exec.block_on(poll_multiplies_6_7)
expect(result).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)


</details>
