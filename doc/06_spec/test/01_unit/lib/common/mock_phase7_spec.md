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

1. expect scheduler get pending count


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

1. expect scheduler get pending count


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

1. expect scheduler get pending count


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

1. expect scheduler get pending count


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

1. expect scheduler get pending count


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

1. scheduler schedule
2. scheduler schedule
3. scheduler schedule
4. Some


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

1. scheduler schedule
2. scheduler schedule
3. scheduler schedule
4. scheduler execute all
5. expect scheduler get pending count


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

1. scheduler execute all
2. expect scheduler verify execution order


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

1. Some


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

1. scheduler schedule
2. scheduler reset
3. expect scheduler get pending count


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

1. expect policy calculate delay
2. expect policy calculate delay
3. expect policy calculate delay


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

1. expect policy calculate delay
2. expect policy calculate delay
3. expect policy calculate delay


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

1. policy set max delay
2. expect policy calculate delay


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

1. policy record attempt
2. expect policy get attempt count
3. expect policy was successful


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

1. policy record attempt
2. expect policy get attempt count
3. expect not policy was successful


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

1. expect policy should retry
2. policy record attempt
3. expect policy should retry
4. policy record attempt
5. expect policy should retry
6. policy record attempt
7. expect not policy should retry


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

1. policy record attempt
2. policy record attempt
3. policy record attempt
4. expect policy get total delay


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

1. policy record attempt
2. policy reset
3. expect policy get attempt count


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

1. expect limiter try acquire
2. expect limiter try acquire
3. expect limiter try acquire
4. expect not limiter try acquire


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

1. expect limiter can proceed
2. limiter try acquire
3. limiter try acquire
4. expect not limiter can proceed


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

1. expect limiter get remaining requests
2. limiter try acquire
3. limiter try acquire
4. expect limiter get remaining requests


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

1. limiter try acquire
2. limiter try acquire
3. expect not limiter can proceed
4. limiter advance time
5. expect limiter can proceed


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

1. expect limiter get wait time
2. limiter try acquire
3. expect limiter get wait time


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

1. limiter try acquire
2. limiter try acquire
3. limiter reset
4. expect limiter get remaining requests


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

1. timeout start
2. timeout advance
3. expect timeout remaining time


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

1. timeout start
2. timeout advance
3. expect timeout has timed out


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

1. timeout start
2. timeout advance


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

1. timeout start
2. timeout advance


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

1. timeout start
2. timeout advance
3. timeout reset
4. expect not timeout has timed out
5. expect timeout remaining time


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

1. expect tracker get start order


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

1. tracker record start
2. tracker advance time
3. tracker record end
4. expect tracker get start order
5. expect tracker get end order


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

1. tracker record start
2. tracker advance time
3. tracker record start
4. expect tracker verify started before
5. expect not tracker verify started before


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

1. tracker record start
2. tracker record start
3. tracker advance time
4. tracker record end
5. tracker advance time
6. tracker record end
7. expect tracker verify completed before


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

1. tracker record start
2. tracker advance time
3. tracker record start
4. tracker advance time
5. tracker record start
6. expect concurrent len


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

1. tracker record start
2. tracker record start
3. tracker record end
4. tracker record end


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

1. tracker record start
2. tracker reset
3. expect tracker get start order


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

1. expect controller try start
2. expect controller try start
3. expect not controller try start


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

1. expect controller can start
2. controller try start
3. expect not controller can start


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

1. controller try start
2. controller try start
3. expect controller get waiting count


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

1. controller try start
2. controller try start
3. controller complete
4. expect controller get waiting count


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

1. controller try start
2. controller try start
3. controller complete
4. expect controller get completed count


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

1. controller try start
2. controller reset


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

1. debouncer call
2. debouncer advance time
3. debouncer call
4. debouncer advance time
5. debouncer call
6. debouncer advance time
7. expect executed len


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

1. debouncer call
2. expect debouncer has pending
3. debouncer advance time
4. expect not debouncer has pending
5. expect debouncer get execution count


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

1. debouncer call
2. debouncer advance time
3. debouncer call
4. debouncer advance time
5. expect debouncer get execution count


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

1. debouncer call
2. debouncer advance time
3. debouncer reset
4. expect debouncer get execution count


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

1. expect throttler call
2. expect throttler get execution count


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

1. expect throttler call
2. expect not throttler call
3. expect not throttler call
4. expect throttler get execution count


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

1. throttler call
2. throttler advance time
3. expect throttler call
4. expect throttler get execution count


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

1. throttler call
2. throttler call
3. throttler call


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

1. throttler call
2. throttler call
3. throttler reset
4. expect throttler get execution count


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

1. retry record attempt
2. retry record attempt


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

1. controller try start
2. tracker record start
3. controller try start
4. tracker record start
5. controller try start
6. tracker advance time
7. tracker record end
8. controller complete
9. tracker record start
10. expect controller active tasks len


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

1. timeout reset
2. timeout start
3. timeout advance
4. retry record attempt
5. retry record attempt
6. expect retry get attempt count
7. expect not retry was successful


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

1. debouncer call
2. debouncer advance time
3. debouncer call
4. debouncer advance time
5. scheduler schedule
6. scheduler execute all
7. expect scheduler get pending count


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
