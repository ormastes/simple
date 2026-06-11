# Async Specification

> <details>

<!-- sdn-diagram:id=async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Specification

## Scenarios

### Poll<T>

#### should create ready poll

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll.ready(42)
expect(p.is_ready()).to_equal(true)
expect(p.is_pending()).to_equal(false)
```

</details>

#### should create pending poll

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll.pending()
expect(p.is_ready()).to_equal(false)
expect(p.is_pending()).to_equal(true)
```

</details>

#### should unwrap ready value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll.ready(42)
expect(p.unwrap()).to_equal(42)
```

</details>

#### should reject unwrap of pending value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll.pending()
match unwrap_checked(p):
    case Ok(_): expect(true).to_equal(false)
    case Err(msg): expect(msg).to_equal("Poll is pending")
```

</details>

### Future<T>

#### should create ready future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(42)
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(42)
```

</details>

#### should create pending future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending()
expect(f.is_ready()).to_equal(false)
expect(f.poll().is_pending()).to_equal(true)
```

</details>

#### should poll ready future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(7)
expect(f.poll().is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(7)
```

</details>

#### should poll pending future

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending()
expect(f.poll().is_pending()).to_equal(true)
```

</details>

#### should transform future value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(21)
val mapped = f.map(_1 * 2)
expect(mapped.is_ready()).to_equal(true)
expect(mapped.poll().unwrap()).to_equal(42)
```

</details>

#### should chain map operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(5)
val mapped = f.map(_1 + 1).map(_1 * 10)
expect(mapped.poll().unwrap()).to_equal(60)
```

</details>

### Promise<T>

#### should create promise-future pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.is_completed()).to_equal(false)
```

</details>

#### should complete promise

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, promise) = Promise.new()
expect(promise.complete(11)).to_equal(true)
expect(promise.is_completed()).to_equal(true)
```

</details>

#### should not complete twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, promise) = Promise.new()
expect(promise.complete(11)).to_equal(true)
expect(promise.complete(22)).to_equal(false)
```

</details>

#### should make future ready after completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(33)).to_equal(true)
expect(future.is_ready()).to_equal(true)
expect(future.poll().unwrap()).to_equal(33)
```

</details>

### Task

#### should create task from function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task.new(make_task_ready_1)
expect(task.id).to_be_greater_than(-1)
expect(task.is_completed()).to_equal(false)
```

</details>

#### should create task with priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task.with_priority(make_task_ready_1, 7)
expect(task.priority).to_equal(7)
```

</details>

#### should start as pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task.new(make_task_ready_1)
expect(task.state.is_completed()).to_equal(false)
expect(task.is_running()).to_equal(false)
```

</details>

#### should track completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task.new(make_task_ready_1)
expect(task.future.is_ready()).to_equal(true)
expect(task.future.poll().unwrap()).to_equal(1)
```

</details>

### Executor

#### should create empty executor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
expect(executor.task_count()).to_equal(0)
expect(executor.is_running()).to_equal(false)
```

</details>

#### should spawn single task

1. executor spawn
   - Expected: executor.task_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
expect(executor.task_count()).to_equal(1)
```

</details>

#### should spawn multiple tasks

1. executor spawn
2. executor spawn
   - Expected: executor.task_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
expect(executor.task_count()).to_equal(2)
```

</details>

#### should run single ready task

1. executor spawn
2. executor run
   - Expected: executor.task_count() equals `0`
   - Expected: executor.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.run()
expect(executor.task_count()).to_equal(0)
expect(executor.is_running()).to_equal(false)
```

</details>

#### should run multiple tasks

1. executor spawn
2. executor spawn
3. executor run
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
executor.run()
expect(executor.task_count()).to_equal(0)
```

</details>

#### should run one iteration

1. executor spawn
2. executor run iteration
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.run_iteration()
expect(executor.task_count()).to_equal(0)
```

</details>

#### should wake suspended task

1. executor spawn
   - Expected: executor.task_count() equals `1`
   - Expected: promise.complete(99) is true
2. executor run
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
val executor = Executor.new()
val task = Task.new(\: future)
executor.spawn(task)
expect(executor.task_count()).to_equal(1)
expect(promise.complete(99)).to_equal(true)
executor.run()
expect(executor.task_count()).to_equal(0)
```

</details>

### Scheduler

#### should create empty scheduler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
expect(scheduler.pending_count()).to_equal(0)
```

</details>

#### should schedule high priority task

1. scheduler schedule
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
expect(scheduler.pending_count()).to_equal(1)
```

</details>

#### should schedule normal priority task

1. scheduler schedule
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 0))
expect(scheduler.pending_count()).to_equal(1)
```

</details>

#### should schedule low priority task

1. scheduler schedule
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
expect(scheduler.pending_count()).to_equal(1)
```

</details>

#### should schedule mixed priority tasks

1. scheduler schedule
2. scheduler schedule
3. scheduler schedule
   - Expected: scheduler.pending_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
expect(scheduler.pending_count()).to_equal(3)
```

</details>

#### should run all scheduled tasks

1. scheduler schedule
2. scheduler schedule
3. scheduler schedule
4. scheduler run
   - Expected: scheduler.pending_count() equals `0`
   - Expected: scheduler.executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
scheduler.run()
expect(scheduler.pending_count()).to_equal(0)
expect(scheduler.executor.task_count()).to_equal(0)
```

</details>

### AsyncIO

#### should create async I/O runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io = AsyncIO.new()
expect(io.executor.task_count()).to_equal(0)
```

</details>

#### should create yield future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AsyncIO.new().yield_now()
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(0)
```

</details>

#### should create sleep future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AsyncIO.new().sleep(25)
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(25)
```

</details>

### Utility Functions

#### should spawn task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = spawn(make_task_ready_1)
expect(task.is_completed()).to_equal(false)
expect(task.future.poll().unwrap()).to_equal(1)
```

</details>

#### should join multiple futures

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val joined = join([Future.from_value(1), Future.from_value(2)])
expect(joined.is_ready()).to_equal(true)
expect(joined.poll().unwrap()).to_equal(2)
```

</details>

#### should select first ready future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selected = select([Future.pending(), Future.from_value(7)])
expect(selected.is_ready()).to_equal(true)
expect(selected.poll().unwrap()).to_equal(7)
```

</details>

### Integration

#### should complete async workflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(123)).to_equal(true)
expect(future.poll().unwrap()).to_equal(123)
```

</details>

#### should execute task to completion

1. executor spawn
2. executor run
   - Expected: executor.task_count() equals `0`
   - Expected: promise.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
val (_, promise) = Promise.new()
val task = Task.new(\: Future.from_value(1))
executor.spawn(task)
executor.run()
expect(executor.task_count()).to_equal(0)
expect(promise.is_completed()).to_equal(false)
```

</details>

#### should run high priority first

1. scheduler schedule
2. scheduler schedule
3. scheduler run
   - Expected: scheduler.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.run()
expect(scheduler.pending_count()).to_equal(0)
```

</details>

#### should chain future transformations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(3)
val chained = f.map(_1 + 2).then(Future.from_value(_1 * 4))
expect(chained.poll().unwrap()).to_equal(20)
```

</details>

### Use Cases

#### should compute value asynchronously

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
expect(promise.complete(88)).to_equal(true)
expect(future.is_ready()).to_equal(true)
expect(future.poll().unwrap()).to_equal(88)
```

</details>

#### should run multiple tasks concurrently

1. executor spawn
2. executor spawn
3. executor run
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
executor.run()
expect(executor.task_count()).to_equal(0)
```

</details>

#### should prioritize urgent tasks

1. scheduler schedule
2. scheduler schedule
   - Expected: scheduler.pending_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 1))
expect(scheduler.pending_count()).to_equal(2)
```

</details>

#### should delay execution with promise

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(9)).to_equal(true)
expect(future.is_ready()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Poll<T>
- Future<T>
- Promise<T>
- Task
- Executor
- Scheduler
- AsyncIO
- Utility Functions
- Integration
- Use Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
