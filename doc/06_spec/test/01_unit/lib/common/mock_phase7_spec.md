# Mock Phase7 Specification

> <details>

<!-- sdn-diagram:id=mock_phase7_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_phase7_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_phase7_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_phase7_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Phase7 Specification

## Scenarios

### Mock Library - Phase 7 (Advanced Scheduling)

#### TaskPriority

#### defines priority levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val critical = TaskPriority.Critical
val high = TaskPriority.High
val normal = TaskPriority.Normal
val low = TaskPriority.Low
val background = TaskPriority.Background
expect true
```

</details>

#### TaskScheduler - Basic

#### creates task scheduler

- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
expect scheduler.get_pending_count() == 0
```

</details>

#### schedules task with priority

- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id = scheduler.schedule("task1", TaskPriority.Normal, 100)
expect id == 0
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules immediate task

- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_immediate("urgent")
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules delayed task

- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_delayed("later", 500)
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules background task

- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_background("bg_task", 1000)
expect scheduler.get_pending_count() == 1
```

</details>

#### TaskScheduler - Execution

#### executes next task by priority

- scheduler schedule
- scheduler schedule
- scheduler schedule
- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
scheduler.schedule("low", TaskPriority.Low, 100)
scheduler.schedule("high", TaskPriority.High, 100)
scheduler.schedule("critical", TaskPriority.Critical, 100)
match scheduler.execute_next():
    Some(task): expect task.name == "critical"
    nil: fail "Expected task"
```

</details>

#### executes all tasks

- scheduler schedule
- scheduler schedule
- scheduler schedule
- scheduler execute all
- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
scheduler.schedule("task1", TaskPriority.Normal, 50)
scheduler.schedule("task2", TaskPriority.Normal, 50)
scheduler.schedule("task3", TaskPriority.Normal, 50)
scheduler.execute_all()
expect scheduler.get_pending_count() == 0
```

</details>

#### tracks execution order

- scheduler execute all
- expect scheduler verify execution order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id1 = scheduler.schedule("critical", TaskPriority.Critical, 10)
val id2 = scheduler.schedule("normal", TaskPriority.Normal, 10)
val id3 = scheduler.schedule("high", TaskPriority.High, 10)
scheduler.execute_all()
expect scheduler.verify_execution_order([id1, id3, id2])
```

</details>

#### gets task by id

- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val id = scheduler.schedule("findme", TaskPriority.Normal, 200)
match scheduler.get_task(id):
    Some(task): expect task.name == "findme"
    nil: fail "Expected task"
```

</details>

#### resets scheduler

- scheduler schedule
- scheduler reset
- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
scheduler.schedule("task", TaskPriority.Normal, 100)
scheduler.reset()
expect scheduler.get_pending_count() == 0
```

</details>

#### RetryPolicy - Basic

#### creates retry policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.new(3)
expect policy.max_attempts == 3
```

</details>

#### creates no-retry policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.no_retry()
expect policy.max_attempts == 1
```

</details>

#### creates linear backoff policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_linear_backoff(5, 100)
expect policy.max_attempts == 5
expect policy.base_delay_ms == 100
```

</details>

#### creates exponential backoff policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_exponential_backoff(4, 50)
expect policy.max_attempts == 4
expect policy.base_delay_ms == 50
```

</details>

#### RetryPolicy - Backoff Calculation

#### calculates linear backoff

- expect policy calculate delay
- expect policy calculate delay
- expect policy calculate delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_linear_backoff(5, 100)
expect policy.calculate_delay(1) == 100
expect policy.calculate_delay(2) == 200
expect policy.calculate_delay(3) == 300
```

</details>

#### calculates exponential backoff

- expect policy calculate delay
- expect policy calculate delay
- expect policy calculate delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_exponential_backoff(5, 100)
expect policy.calculate_delay(1) == 100
expect policy.calculate_delay(2) == 200
expect policy.calculate_delay(3) == 400
```

</details>

#### respects max delay

- policy set max delay
- expect policy calculate delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_exponential_backoff(10, 100)
policy.set_max_delay(500)
expect policy.calculate_delay(5) <= 500
```

</details>

#### RetryPolicy - Attempt Tracking

#### records successful attempt

- policy record attempt
- expect policy get attempt count
- expect policy was successful


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.new(3)
policy.record_attempt(true, nil)
expect policy.get_attempt_count() == 1
expect policy.was_successful()
```

</details>

#### records failed attempt

- policy record attempt
- expect policy get attempt count
- expect not policy was successful


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.new(3)
policy.record_attempt(false, Some("timeout"))
expect policy.get_attempt_count() == 1
expect not policy.was_successful()
```

</details>

#### determines should retry

- expect policy should retry
- policy record attempt
- expect policy should retry
- policy record attempt
- expect policy should retry
- policy record attempt
- expect not policy should retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.new(3)
expect policy.should_retry()
policy.record_attempt(false, Some("error"))
expect policy.should_retry()
policy.record_attempt(false, Some("error"))
expect policy.should_retry()
policy.record_attempt(false, Some("error"))
expect not policy.should_retry()
```

</details>

#### calculates total delay

- policy record attempt
- policy record attempt
- policy record attempt
- expect policy get total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.with_linear_backoff(3, 100)
policy.record_attempt(false, nil)
policy.record_attempt(false, nil)
policy.record_attempt(true, nil)
expect policy.get_total_delay() == 600
```

</details>

#### resets policy

- policy record attempt
- policy reset
- expect policy get attempt count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy.new(3)
policy.record_attempt(false, nil)
policy.reset()
expect policy.get_attempt_count() == 0
```

</details>

#### RateLimiter - Basic

#### creates rate limiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(10, 1000)
expect limiter.max_requests == 10
expect limiter.window_ms == 1000
```

</details>

#### creates per-second limiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.per_second(5)
expect limiter.max_requests == 5
expect limiter.window_ms == 1000
```

</details>

#### creates per-minute limiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.per_minute(100)
expect limiter.max_requests == 100
expect limiter.window_ms == 60000
```

</details>

#### RateLimiter - Request Handling

#### allows requests within limit

- expect limiter try acquire
- expect limiter try acquire
- expect limiter try acquire
- expect not limiter try acquire


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(3, 1000)
expect limiter.try_acquire()
expect limiter.try_acquire()
expect limiter.try_acquire()
expect not limiter.try_acquire()
```

</details>

#### checks can proceed

- expect limiter can proceed
- limiter try acquire
- limiter try acquire
- expect not limiter can proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(2, 1000)
expect limiter.can_proceed()
limiter.try_acquire()
limiter.try_acquire()
expect not limiter.can_proceed()
```

</details>

#### gets remaining requests

- expect limiter get remaining requests
- limiter try acquire
- limiter try acquire
- expect limiter get remaining requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(5, 1000)
expect limiter.get_remaining_requests() == 5
limiter.try_acquire()
limiter.try_acquire()
expect limiter.get_remaining_requests() == 3
```

</details>

#### cleans up old requests after window

- limiter try acquire
- limiter try acquire
- expect not limiter can proceed
- limiter advance time
- expect limiter can proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(2, 100)
limiter.try_acquire()
limiter.try_acquire()
expect not limiter.can_proceed()
limiter.advance_time(150)
expect limiter.can_proceed()
```

</details>

#### calculates wait time

- expect limiter get wait time
- limiter try acquire
- expect limiter get wait time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(1, 100)
expect limiter.get_wait_time() == 0
limiter.try_acquire()
expect limiter.get_wait_time() == 100
```

</details>

#### resets limiter

- limiter try acquire
- limiter try acquire
- limiter reset
- expect limiter get remaining requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(2, 1000)
limiter.try_acquire()
limiter.try_acquire()
limiter.reset()
expect limiter.get_remaining_requests() == 2
```

</details>

#### TimeoutController - Basic

#### creates timeout controller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(5000)
expect timeout.timeout_ms == 5000
```

</details>

#### starts and tracks elapsed time

- timeout start
- timeout advance
- expect timeout remaining time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(50)
expect timeout.remaining_time() == 50
```

</details>

#### detects timeout

- timeout start
- timeout advance
- expect timeout has timed out


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(150)
expect timeout.has_timed_out()
```

</details>

#### completes without timeout

- timeout start
- timeout advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(50)
val result = timeout.complete()
expect result.completed
expect not result.timed_out
```

</details>

#### completes with timeout

- timeout start
- timeout advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(150)
val result = timeout.complete()
expect not result.completed
expect result.timed_out
```

</details>

#### resets timeout

- timeout start
- timeout advance
- timeout reset
- expect not timeout has timed out
- expect timeout remaining time


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(150)
timeout.reset()
expect not timeout.has_timed_out()
expect timeout.remaining_time() == 100
```

</details>

#### ExecutionOrderTracker - Basic

#### creates execution order tracker

- expect tracker get start order


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
expect tracker.get_start_order().len() == 0
```

</details>

#### records start and end events

- tracker record start
- tracker advance time
- tracker record end
- expect tracker get start order
- expect tracker get end order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("task1")
tracker.advance_time(50)
tracker.record_end("task1")
expect tracker.get_start_order().len() == 1
expect tracker.get_end_order().len() == 1
```

</details>

#### ExecutionOrderTracker - Verification

#### verifies started before

- tracker record start
- tracker advance time
- tracker record start
- expect tracker verify started before
- expect not tracker verify started before


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("first")
tracker.advance_time(10)
tracker.record_start("second")
expect tracker.verify_started_before("first", "second")
expect not tracker.verify_started_before("second", "first")
```

</details>

#### verifies completed before

- tracker record start
- tracker record start
- tracker advance time
- tracker record end
- tracker advance time
- tracker record end
- expect tracker verify completed before


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("fast")
tracker.record_start("slow")
tracker.advance_time(50)
tracker.record_end("fast")
tracker.advance_time(100)
tracker.record_end("slow")
expect tracker.verify_completed_before("fast", "slow")
```

</details>

#### gets concurrent tasks at time

- tracker record start
- tracker advance time
- tracker record start
- tracker advance time
- tracker record start
- expect concurrent len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("task1")
tracker.advance_time(10)
tracker.record_start("task2")
tracker.advance_time(10)
tracker.record_start("task3")
val concurrent = tracker.get_concurrent_at(15)
expect concurrent.len() == 2
```

</details>

#### gets start and end order

- tracker record start
- tracker record start
- tracker record end
- tracker record end


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("a")
tracker.record_start("b")
tracker.record_end("a")
tracker.record_end("b")
val starts = tracker.get_start_order()
expect starts[0] == "a"
expect starts[1] == "b"
```

</details>

#### resets tracker

- tracker record start
- tracker reset
- expect tracker get start order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = ExecutionOrderTracker.new()
tracker.record_start("task")
tracker.reset()
expect tracker.get_start_order().len() == 0
```

</details>

#### ConcurrencyController - Basic

#### creates concurrency controller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(3)
expect controller.max_concurrent == 3
```

</details>

#### allows starting within limit

- expect controller try start
- expect controller try start
- expect not controller try start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(2)
expect controller.try_start("task1")
expect controller.try_start("task2")
expect not controller.try_start("task3")
```

</details>

#### checks can start

- expect controller can start
- controller try start
- expect not controller can start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(1)
expect controller.can_start()
controller.try_start("task")
expect not controller.can_start()
```

</details>

#### ConcurrencyController - Queue Management

#### queues tasks when at limit

- controller try start
- controller try start
- expect controller get waiting count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(1)
controller.try_start("active")
controller.try_start("waiting")
expect controller.active_count == 1
expect controller.get_waiting_count() == 1
```

</details>

#### starts waiting task on completion

- controller try start
- controller try start
- controller complete
- expect controller get waiting count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(1)
controller.try_start("first")
controller.try_start("second")
controller.complete("first")
expect controller.active_count == 1
expect controller.get_waiting_count() == 0
val active = controller.active_tasks
expect active[0] == "second"
```

</details>

#### tracks completed tasks

- controller try start
- controller try start
- controller complete
- expect controller get completed count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(2)
controller.try_start("a")
controller.try_start("b")
controller.complete("a")
expect controller.get_completed_count() == 1
```

</details>

#### resets controller

- controller try start
- controller reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(2)
controller.try_start("task")
controller.reset()
expect controller.active_count == 0
```

</details>

#### Debouncer - Basic

#### creates debouncer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debouncer = Debouncer.new(100)
expect debouncer.delay_ms == 100
```

</details>

#### debounces rapid calls

- debouncer call
- debouncer advance time
- debouncer call
- debouncer advance time
- debouncer call
- debouncer advance time
- expect executed len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debouncer = Debouncer.new(100)
debouncer.call("first")
debouncer.advance_time(50)
debouncer.call("second")
debouncer.advance_time(50)
debouncer.call("third")
debouncer.advance_time(150)
val executed = debouncer.executed_values
expect executed.len() == 1
expect executed[0] == "third"
```

</details>

#### executes after delay

- debouncer call
- expect debouncer has pending
- debouncer advance time
- expect not debouncer has pending
- expect debouncer get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debouncer = Debouncer.new(100)
debouncer.call("value")
expect debouncer.has_pending()
debouncer.advance_time(150)
expect not debouncer.has_pending()
expect debouncer.get_execution_count() == 1
```

</details>

#### tracks execution count

- debouncer call
- debouncer advance time
- debouncer call
- debouncer advance time
- expect debouncer get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debouncer = Debouncer.new(50)
debouncer.call("a")
debouncer.advance_time(100)
debouncer.call("b")
debouncer.advance_time(100)
expect debouncer.get_execution_count() == 2
```

</details>

#### resets debouncer

- debouncer call
- debouncer advance time
- debouncer reset
- expect debouncer get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debouncer = Debouncer.new(100)
debouncer.call("value")
debouncer.advance_time(150)
debouncer.reset()
expect debouncer.get_execution_count() == 0
```

</details>

#### Throttler - Basic

#### creates throttler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
expect throttler.interval_ms == 100
```

</details>

#### allows first call

- expect throttler call
- expect throttler get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
expect throttler.call("first")
expect throttler.get_execution_count() == 1
```

</details>

#### throttles rapid calls

- expect throttler call
- expect not throttler call
- expect not throttler call
- expect throttler get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
expect throttler.call("first")
expect not throttler.call("second")
expect not throttler.call("third")
expect throttler.get_execution_count() == 1
```

</details>

#### allows call after interval

- throttler call
- throttler advance time
- expect throttler call
- expect throttler get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
throttler.call("first")
throttler.advance_time(150)
expect throttler.call("second")
expect throttler.get_execution_count() == 2
```

</details>

#### tracks dropped calls

- throttler call
- throttler call
- throttler call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
throttler.call("ok")
throttler.call("dropped1")
throttler.call("dropped2")
expect throttler.dropped_count == 2
```

</details>

#### resets throttler

- throttler call
- throttler call
- throttler reset
- expect throttler get execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val throttler = Throttler.new(100)
throttler.call("value")
throttler.call("dropped")
throttler.reset()
expect throttler.get_execution_count() == 0
expect throttler.dropped_count == 0
```

</details>

#### Complex Scheduling Scenarios

#### simulates API with rate limiting and retry

- retry record attempt
- retry record attempt


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limiter = RateLimiter.new(2, 1000)
val retry = RetryPolicy.with_exponential_backoff(3, 100)
var success = false
while retry.should_retry() and not success:
    if limiter.try_acquire():
        success = true
        retry.record_attempt(true, nil)
    else:
        retry.record_attempt(false, Some("rate limited"))
expect success
```

</details>

#### tracks concurrent async operations

- controller try start
- tracker record start
- controller try start
- tracker record start
- controller try start
- tracker advance time
- tracker record end
- controller complete
- tracker record start
- expect controller active tasks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = ConcurrencyController.new(2)
val tracker = ExecutionOrderTracker.new()
controller.try_start("op1")
tracker.record_start("op1")
controller.try_start("op2")
tracker.record_start("op2")
controller.try_start("op3")
tracker.advance_time(100)
tracker.record_end("op1")
controller.complete("op1")
tracker.record_start("op3")
expect controller.active_tasks.len() == 2
```

</details>

#### handles timeout with retry

- timeout reset
- timeout start
- timeout advance
- retry record attempt
- retry record attempt
- expect retry get attempt count
- expect not retry was successful


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = TimeoutController.new(100)
val retry = RetryPolicy.new(3)
var completed = false
while retry.should_retry() and not completed:
    timeout.reset()
    timeout.start()
    timeout.advance(150)
    if timeout.has_timed_out():
        retry.record_attempt(false, Some("timeout"))
    else:
        retry.record_attempt(true, nil)
        completed = true
expect retry.get_attempt_count() == 3
expect not retry.was_successful()
```

</details>

#### priority scheduling with debounce

- debouncer call
- debouncer advance time
- debouncer call
- debouncer advance time
- scheduler schedule
- scheduler execute all
- expect scheduler get pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = TaskScheduler.new()
val debouncer = Debouncer.new(50)
debouncer.call("input1")
debouncer.advance_time(30)
debouncer.call("input2")
debouncer.advance_time(100)
val values = debouncer.executed_values
if values.len() > 0:
    scheduler.schedule(values[0], TaskPriority.High, 10)
scheduler.execute_all()
expect scheduler.get_pending_count() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mock_phase7_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mock Library - Phase 7 (Advanced Scheduling)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
