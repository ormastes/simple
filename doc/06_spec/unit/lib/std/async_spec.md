# async_spec

> Purpose: Verify Poll<T>.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_spec

Purpose: Verify Poll<T>.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/async_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Poll<T>.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Poll<T>

#### should create ready poll

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create ready poll
- Verify: should create ready poll
   - Expected: p.is_ready() is true
   - Expected: p.is_pending() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create ready poll")
step("Verify: should create ready poll")
# @req: REQ-LIB-ASYNC-001
val p = Poll.ready(42)
expect(p.is_ready()).to_equal(true)
expect(p.is_pending()).to_equal(false)
```

</details>

#### should create pending poll

- should create pending poll
- Verify: should create pending poll
   - Expected: p.is_ready() is false
   - Expected: p.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create pending poll")
step("Verify: should create pending poll")
val p = Poll.pending()
expect(p.is_ready()).to_equal(false)
expect(p.is_pending()).to_equal(true)
```

</details>

#### should unwrap ready value

- should unwrap ready value
- Verify: should unwrap ready value
   - Expected: p.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should unwrap ready value")
step("Verify: should unwrap ready value")
val p = Poll.ready(42)
expect(p.unwrap()).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should reject unwrap of pending value

- should reject unwrap of pending value
- Verify: should reject unwrap of pending value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject unwrap of pending value")
step("Verify: should reject unwrap of pending value")
val p = Poll.pending()
match unwrap_checked(p):
    case Ok(_): expect(true).to_equal(false)
    case Err(msg): expect(msg).to_equal("Poll is pending")
```

</details>

### Future<T>

#### should create ready future

- should create ready future
- Verify: should create ready future
   - Expected: f.is_ready() is true
   - Expected: f.poll().unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create ready future")
step("Verify: should create ready future")
val f = Future.from_value(42)
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should create pending future

- should create pending future
- Verify: should create pending future
   - Expected: f.is_ready() is false
   - Expected: f.poll().is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create pending future")
step("Verify: should create pending future")
val f = Future.pending()
expect(f.is_ready()).to_equal(false)
expect(f.poll().is_pending()).to_equal(true)
```

</details>

#### should poll ready future

- should poll ready future
- Verify: should poll ready future
   - Expected: f.poll().is_ready() is true
   - Expected: f.poll().unwrap() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should poll ready future")
step("Verify: should poll ready future")
val f = Future.from_value(7)
expect(f.poll().is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(7)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should poll pending future

- should poll pending future
- Verify: should poll pending future
   - Expected: f.poll().is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should poll pending future")
step("Verify: should poll pending future")
val f = Future.pending()
expect(f.poll().is_pending()).to_equal(true)
```

</details>

#### should transform future value

- should transform future value
- Verify: should transform future value
   - Expected: mapped.is_ready() is true
   - Expected: mapped.poll().unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should transform future value")
step("Verify: should transform future value")
val f = Future.from_value(21)
val mapped = f.map(_1 * 2)
expect(mapped.is_ready()).to_equal(true)
expect(mapped.poll().unwrap()).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should chain map operations

- should chain map operations
- Verify: should chain map operations
   - Expected: mapped.poll().unwrap() equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should chain map operations")
step("Verify: should chain map operations")
val f = Future.from_value(5)
val mapped = f.map(_1 + 1).map(_1 * 10)
expect(mapped.poll().unwrap()).to_equal(60)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Promise<T>

#### should create promise-future pair

- should create promise-future pair
- Verify: should create promise-future pair
   - Expected: future.is_ready() is false
   - Expected: promise.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create promise-future pair")
step("Verify: should create promise-future pair")
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.is_completed()).to_equal(false)
```

</details>

#### should complete promise

- should complete promise
- Verify: should complete promise
   - Expected: promise.complete(11) is true
   - Expected: promise.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should complete promise")
step("Verify: should complete promise")
val (_, promise) = Promise.new()
expect(promise.complete(11)).to_equal(true)
expect(promise.is_completed()).to_equal(true)
```

</details>

#### should not complete twice

- should not complete twice
- Verify: should not complete twice
   - Expected: promise.complete(11) is true
   - Expected: promise.complete(22) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not complete twice")
step("Verify: should not complete twice")
val (_, promise) = Promise.new()
expect(promise.complete(11)).to_equal(true)
expect(promise.complete(22)).to_equal(false)
```

</details>

#### should make future ready after completion

- should make future ready after completion
- Verify: should make future ready after completion
   - Expected: future.is_ready() is false
   - Expected: promise.complete(33) is true
   - Expected: future.is_ready() is true
   - Expected: future.poll().unwrap() equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should make future ready after completion")
step("Verify: should make future ready after completion")
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(33)).to_equal(true)
expect(future.is_ready()).to_equal(true)
expect(future.poll().unwrap()).to_equal(33)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Task

#### should create task from function

- should create task from function
- Verify: should create task from function
   - Expected: task.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create task from function")
step("Verify: should create task from function")
val task = Task.new(make_task_ready_1)
expect(task.id).to_be_greater_than(-1)
expect(task.is_completed()).to_equal(false)
```

</details>

#### should create task with priority

- should create task with priority
- Verify: should create task with priority
   - Expected: task.priority equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create task with priority")
step("Verify: should create task with priority")
val task = Task.with_priority(make_task_ready_1, 7)
expect(task.priority).to_equal(7)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should start as pending

- should start as pending
- Verify: should start as pending
   - Expected: task.state.is_completed() is false
   - Expected: task.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should start as pending")
step("Verify: should start as pending")
val task = Task.new(make_task_ready_1)
expect(task.state.is_completed()).to_equal(false)
expect(task.is_running()).to_equal(false)
```

</details>

#### should track completion

- should track completion
- Verify: should track completion
   - Expected: task.future.is_ready() is true
   - Expected: task.future.poll().unwrap() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should track completion")
step("Verify: should track completion")
val task = Task.new(make_task_ready_1)
expect(task.future.is_ready()).to_equal(true)
expect(task.future.poll().unwrap()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Executor

#### should create empty executor

- should create empty executor
- Verify: should create empty executor
   - Expected: executor.task_count() equals `0`
   - Expected: executor.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create empty executor")
step("Verify: should create empty executor")
val executor = Executor.new()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(executor.is_running()).to_equal(false)
```

</details>

#### should spawn single task

- should spawn single task
- Verify: should spawn single task
   - Expected: executor.task_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should spawn single task")
step("Verify: should spawn single task")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
expect(executor.task_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should spawn multiple tasks

- should spawn multiple tasks
- Verify: should spawn multiple tasks
   - Expected: executor.task_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should spawn multiple tasks")
step("Verify: should spawn multiple tasks")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
expect(executor.task_count()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should run single ready task

- should run single ready task
- Verify: should run single ready task
   - Expected: executor.task_count() equals `0`
   - Expected: executor.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run single ready task")
step("Verify: should run single ready task")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.run()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(executor.is_running()).to_equal(false)
```

</details>

#### should run multiple tasks

- should run multiple tasks
- Verify: should run multiple tasks
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run multiple tasks")
step("Verify: should run multiple tasks")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
executor.run()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should run one iteration

- should run one iteration
- Verify: should run one iteration
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run one iteration")
step("Verify: should run one iteration")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.run_iteration()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should wake suspended task

- should wake suspended task
- Verify: should wake suspended task
   - Expected: executor.task_count() equals `1`
   - Expected: promise.complete(99) is true
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should wake suspended task")
step("Verify: should wake suspended task")
val (future, promise) = Promise.new()
val executor = Executor.new()
val task = Task.new(\: future)
executor.spawn(task)
expect(executor.task_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
expect(promise.complete(99)).to_equal(true)
executor.run()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Scheduler

#### should create empty scheduler

- should create empty scheduler
- Verify: should create empty scheduler
   - Expected: scheduler.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create empty scheduler")
step("Verify: should create empty scheduler")
val scheduler = Scheduler.new()
expect(scheduler.pending_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should schedule high priority task

- should schedule high priority task
- Verify: should schedule high priority task
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should schedule high priority task")
step("Verify: should schedule high priority task")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
expect(scheduler.pending_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should schedule normal priority task

- should schedule normal priority task
- Verify: should schedule normal priority task
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should schedule normal priority task")
step("Verify: should schedule normal priority task")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 0))
expect(scheduler.pending_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should schedule low priority task

- should schedule low priority task
- Verify: should schedule low priority task
   - Expected: scheduler.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should schedule low priority task")
step("Verify: should schedule low priority task")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
expect(scheduler.pending_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should schedule mixed priority tasks

- should schedule mixed priority tasks
- Verify: should schedule mixed priority tasks
   - Expected: scheduler.pending_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should schedule mixed priority tasks")
step("Verify: should schedule mixed priority tasks")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
expect(scheduler.pending_count()).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should run all scheduled tasks

- should run all scheduled tasks
- Verify: should run all scheduled tasks
   - Expected: scheduler.pending_count() equals `0`
   - Expected: scheduler.executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run all scheduled tasks")
step("Verify: should run all scheduled tasks")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.schedule(Task.with_priority(make_task_ready_1, -1))
scheduler.run()
expect(scheduler.pending_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(scheduler.executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### AsyncIO

#### should create async I/O runtime

- should create async I/O runtime
- Verify: should create async I/O runtime
   - Expected: io.executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create async I/O runtime")
step("Verify: should create async I/O runtime")
val io = AsyncIO.new()
expect(io.executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should create yield future

- should create yield future
- Verify: should create yield future
   - Expected: f.is_ready() is true
   - Expected: f.poll().unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create yield future")
step("Verify: should create yield future")
val f = AsyncIO.new().yield_now()
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should create sleep future

- should create sleep future
- Verify: should create sleep future
   - Expected: f.is_ready() is true
   - Expected: f.poll().unwrap() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create sleep future")
step("Verify: should create sleep future")
val f = AsyncIO.new().sleep(25)
expect(f.is_ready()).to_equal(true)
expect(f.poll().unwrap()).to_equal(25)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Utility Functions

#### should spawn task

- should spawn task
- Verify: should spawn task
   - Expected: task.is_completed() is false
   - Expected: task.future.poll().unwrap() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should spawn task")
step("Verify: should spawn task")
val task = spawn(make_task_ready_1)
expect(task.is_completed()).to_equal(false)
expect(task.future.poll().unwrap()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should join multiple futures

- should join multiple futures
- Verify: should join multiple futures
   - Expected: joined.is_ready() is true
   - Expected: joined.poll().unwrap() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should join multiple futures")
step("Verify: should join multiple futures")
val joined = join([Future.from_value(1), Future.from_value(2)])
expect(joined.is_ready()).to_equal(true)
expect(joined.poll().unwrap()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should select first ready future

- should select first ready future
- Verify: should select first ready future
   - Expected: selected.is_ready() is true
   - Expected: selected.poll().unwrap() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should select first ready future")
step("Verify: should select first ready future")
val selected = select([Future.pending(), Future.from_value(7)])
expect(selected.is_ready()).to_equal(true)
expect(selected.poll().unwrap()).to_equal(7)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Integration

#### should complete async workflow

- should complete async workflow
- Verify: should complete async workflow
   - Expected: future.is_ready() is false
   - Expected: promise.complete(123) is true
   - Expected: future.poll().unwrap() equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should complete async workflow")
step("Verify: should complete async workflow")
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(123)).to_equal(true)
expect(future.poll().unwrap()).to_equal(123)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should execute task to completion

- should execute task to completion
- Verify: should execute task to completion
   - Expected: executor.task_count() equals `0`
   - Expected: promise.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should execute task to completion")
step("Verify: should execute task to completion")
val executor = Executor.new()
val (_, promise) = Promise.new()
val task = Task.new(\: Future.from_value(1))
executor.spawn(task)
executor.run()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(promise.is_completed()).to_equal(false)
```

</details>

#### should run high priority first

- should run high priority first
- Verify: should run high priority first
   - Expected: scheduler.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run high priority first")
step("Verify: should run high priority first")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 0))
scheduler.run()
expect(scheduler.pending_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should chain future transformations

- should chain future transformations
- Verify: should chain future transformations
   - Expected: chained.poll().unwrap() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should chain future transformations")
step("Verify: should chain future transformations")
val f = Future.from_value(3)
val chained = f.map(_1 + 2).then(Future.from_value(_1 * 4))
expect(chained.poll().unwrap()).to_equal(20)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Use Cases

#### should compute value asynchronously

- should compute value asynchronously
- Verify: should compute value asynchronously
   - Expected: promise.complete(88) is true
   - Expected: future.is_ready() is true
   - Expected: future.poll().unwrap() equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should compute value asynchronously")
step("Verify: should compute value asynchronously")
val (future, promise) = Promise.new()
expect(promise.complete(88)).to_equal(true)
expect(future.is_ready()).to_equal(true)
expect(future.poll().unwrap()).to_equal(88)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should run multiple tasks concurrently

- should run multiple tasks concurrently
- Verify: should run multiple tasks concurrently
   - Expected: executor.task_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run multiple tasks concurrently")
step("Verify: should run multiple tasks concurrently")
val executor = Executor.new()
executor.spawn(Task.new(make_task_ready_1))
executor.spawn(Task.new(make_task_ready_2))
executor.run()
expect(executor.task_count()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should prioritize urgent tasks

- should prioritize urgent tasks
- Verify: should prioritize urgent tasks
   - Expected: scheduler.pending_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should prioritize urgent tasks")
step("Verify: should prioritize urgent tasks")
val scheduler = Scheduler.new()
scheduler.schedule(Task.with_priority(make_task_ready_1, 10))
scheduler.schedule(Task.with_priority(make_task_ready_2, 1))
expect(scheduler.pending_count()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should delay execution with promise

- should delay execution with promise
- Verify: should delay execution with promise
   - Expected: future.is_ready() is false
   - Expected: promise.complete(9) is true
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should delay execution with promise")
step("Verify: should delay execution with promise")
val (future, promise) = Promise.new()
expect(future.is_ready()).to_equal(false)
expect(promise.complete(9)).to_equal(true)
expect(future.is_ready()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-ASYNC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f861933a03c6b10b37d076c84e2a0db1e10dc454f4ee3d3f3554c86788e4449`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f861933a03c6b10b37d076c84e2a0db1e10dc454f4ee3d3f3554c86788e4449`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f861933a03c6b10b37d076c84e2a0db1e10dc454f4ee3d3f3554c86788e4449`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/async_spec.spl
mirror: doc/06_spec/unit/lib/std/async_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/async_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/async_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/async_spec.spl:283:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create ready poll' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/async_spec.spl:283:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create ready poll' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/async_spec.spl:292:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create pending poll' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/async_spec.spl:292:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create pending poll' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/async_spec.spl:300:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should unwrap ready value' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/async_spec.spl:300:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should unwrap ready value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/async_spec.spl:307:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unwrap of pending value' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/async_spec.spl:321:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create ready future' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/async_spec.spl:329:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create pending future' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
