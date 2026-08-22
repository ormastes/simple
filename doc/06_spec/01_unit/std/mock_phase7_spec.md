# mock_phase7_spec

> Verifies the mock phase7 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_phase7_spec

Verifies the mock phase7 behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_phase7_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mock phase7 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Mock Library - Phase 7 (Advanced Scheduling)

#### TaskPriority

#### defines priority levels

- Verify: defines priority levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: defines priority levels")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: creates task scheduler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates task scheduler")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
expect scheduler.get_pending_count() == 0
```

</details>

#### schedules task with priority

- Verify: schedules task with priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: schedules task with priority")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id = scheduler.schedule("task1", TaskPriority.Normal, 100)
expect id == 0
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules immediate task

- Verify: schedules immediate task


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: schedules immediate task")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_immediate("urgent")
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules delayed task

- Verify: schedules delayed task


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: schedules delayed task")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_delayed("later", 500)
expect scheduler.get_pending_count() == 1
```

</details>

#### schedules background task

- Verify: schedules background task


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: schedules background task")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id = scheduler.schedule_background("bg_task", 1000)
expect scheduler.get_pending_count() == 1
```

</details>

#### TaskScheduler - Execution

#### executes next task by priority

- Verify: executes next task by priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: executes next task by priority")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: executes all tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: executes all tasks")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
scheduler.schedule("task1", TaskPriority.Normal, 50)
scheduler.schedule("task2", TaskPriority.Normal, 50)
scheduler.schedule("task3", TaskPriority.Normal, 50)
scheduler.execute_all()
expect scheduler.get_pending_count() == 0
```

</details>

#### tracks execution order

- Verify: tracks execution order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: tracks execution order")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id1 = scheduler.schedule("critical", TaskPriority.Critical, 10)
val id2 = scheduler.schedule("normal", TaskPriority.Normal, 10)
val id3 = scheduler.schedule("high", TaskPriority.High, 10)
scheduler.execute_all()
expect scheduler.verify_execution_order([id1, id3, id2])
```

</details>

#### gets task by id

- Verify: gets task by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: gets task by id")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
val id = scheduler.schedule("findme", TaskPriority.Normal, 200)
match scheduler.get_task(id):
    Some(task): expect task.name == "findme"
    nil: fail "Expected task"
```

</details>

#### resets scheduler

- Verify: resets scheduler


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets scheduler")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val scheduler = TaskScheduler.new()
scheduler.schedule("task", TaskPriority.Normal, 100)
scheduler.reset()
expect scheduler.get_pending_count() == 0
```

</details>

#### RetryPolicy - Basic

#### creates retry policy

- Verify: creates retry policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates retry policy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.new(3)
expect policy.max_attempts == 3
```

</details>

#### creates no-retry policy

- Verify: creates no-retry policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates no-retry policy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.no_retry()
expect policy.max_attempts == 1
```

</details>

#### creates linear backoff policy

- Verify: creates linear backoff policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates linear backoff policy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_linear_backoff(5, 100)
expect policy.max_attempts == 5
expect policy.base_delay_ms == 100
```

</details>

#### creates exponential backoff policy

- Verify: creates exponential backoff policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates exponential backoff policy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_exponential_backoff(4, 50)
expect policy.max_attempts == 4
expect policy.base_delay_ms == 50
```

</details>

#### RetryPolicy - Backoff Calculation

#### calculates linear backoff

- Verify: calculates linear backoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: calculates linear backoff")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_linear_backoff(5, 100)
expect policy.calculate_delay(1) == 100
expect policy.calculate_delay(2) == 200
expect policy.calculate_delay(3) == 300
```

</details>

#### calculates exponential backoff

- Verify: calculates exponential backoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: calculates exponential backoff")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_exponential_backoff(5, 100)
expect policy.calculate_delay(1) == 100
expect policy.calculate_delay(2) == 200
expect policy.calculate_delay(3) == 400
```

</details>

#### respects max delay

- Verify: respects max delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: respects max delay")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_exponential_backoff(10, 100)
policy.set_max_delay(500)
expect policy.calculate_delay(5) <= 500
```

</details>

#### RetryPolicy - Attempt Tracking

#### records successful attempt

- Verify: records successful attempt


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: records successful attempt")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.new(3)
policy.record_attempt(true, nil)
expect policy.get_attempt_count() == 1
expect policy.was_successful()
```

</details>

#### records failed attempt

- Verify: records failed attempt


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: records failed attempt")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.new(3)
policy.record_attempt(false, Some("timeout"))
expect policy.get_attempt_count() == 1
expect not policy.was_successful()
```

</details>

#### determines should retry

- Verify: determines should retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: determines should retry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: calculates total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: calculates total delay")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.with_linear_backoff(3, 100)
policy.record_attempt(false, nil)
policy.record_attempt(false, nil)
policy.record_attempt(true, nil)
expect policy.get_total_delay() == 600
```

</details>

#### resets policy

- Verify: resets policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets policy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val policy = RetryPolicy.new(3)
policy.record_attempt(false, nil)
policy.reset()
expect policy.get_attempt_count() == 0
```

</details>

#### RateLimiter - Basic

#### creates rate limiter

- Verify: creates rate limiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates rate limiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(10, 1000)
expect limiter.max_requests == 10
expect limiter.window_ms == 1000
```

</details>

#### creates per-second limiter

- Verify: creates per-second limiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates per-second limiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.per_second(5)
expect limiter.max_requests == 5
expect limiter.window_ms == 1000
```

</details>

#### creates per-minute limiter

- Verify: creates per-minute limiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates per-minute limiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.per_minute(100)
expect limiter.max_requests == 100
expect limiter.window_ms == 60000
```

</details>

#### RateLimiter - Request Handling

#### allows requests within limit

- Verify: allows requests within limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: allows requests within limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(3, 1000)
expect limiter.try_acquire()
expect limiter.try_acquire()
expect limiter.try_acquire()
expect not limiter.try_acquire()
```

</details>

#### checks can proceed

- Verify: checks can proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: checks can proceed")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(2, 1000)
expect limiter.can_proceed()
limiter.try_acquire()
limiter.try_acquire()
expect not limiter.can_proceed()
```

</details>

#### gets remaining requests

- Verify: gets remaining requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: gets remaining requests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(5, 1000)
expect limiter.get_remaining_requests() == 5
limiter.try_acquire()
limiter.try_acquire()
expect limiter.get_remaining_requests() == 3
```

</details>

#### cleans up old requests after window

- Verify: cleans up old requests after window


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: cleans up old requests after window")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(2, 100)
limiter.try_acquire()
limiter.try_acquire()
expect not limiter.can_proceed()
limiter.advance_time(150)
expect limiter.can_proceed()
```

</details>

#### calculates wait time

- Verify: calculates wait time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: calculates wait time")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(1, 100)
expect limiter.get_wait_time() == 0
limiter.try_acquire()
expect limiter.get_wait_time() == 100
```

</details>

#### resets limiter

- Verify: resets limiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets limiter")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val limiter = RateLimiter.new(2, 1000)
limiter.try_acquire()
limiter.try_acquire()
limiter.reset()
expect limiter.get_remaining_requests() == 2
```

</details>

#### TimeoutController - Basic

#### creates timeout controller

- Verify: creates timeout controller


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates timeout controller")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val timeout = TimeoutController.new(5000)
expect timeout.timeout_ms == 5000
```

</details>

#### starts and tracks elapsed time

- Verify: starts and tracks elapsed time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: starts and tracks elapsed time")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(50)
expect timeout.remaining_time() == 50
```

</details>

#### detects timeout

- Verify: detects timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: detects timeout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(150)
expect timeout.has_timed_out()
```

</details>

#### completes without timeout

- Verify: completes without timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: completes without timeout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(50)
val result = timeout.complete()
expect result.completed
expect not result.timed_out
```

</details>

#### completes with timeout

- Verify: completes with timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: completes with timeout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val timeout = TimeoutController.new(100)
timeout.start()
timeout.advance(150)
val result = timeout.complete()
expect not result.completed
expect result.timed_out
```

</details>

#### resets timeout

- Verify: resets timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets timeout")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: creates execution order tracker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates execution order tracker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tracker = ExecutionOrderTracker.new()
expect tracker.get_start_order().len() == 0
```

</details>

#### records start and end events

- Verify: records start and end events


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: records start and end events")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: verifies started before


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: verifies started before")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tracker = ExecutionOrderTracker.new()
tracker.record_start("first")
tracker.advance_time(10)
tracker.record_start("second")
expect tracker.verify_started_before("first", "second")
expect not tracker.verify_started_before("second", "first")
```

</details>

#### verifies completed before

- Verify: verifies completed before


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: verifies completed before")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets concurrent tasks at time


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: gets concurrent tasks at time")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets start and end order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: gets start and end order")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: resets tracker


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets tracker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tracker = ExecutionOrderTracker.new()
tracker.record_start("task")
tracker.reset()
expect tracker.get_start_order().len() == 0
```

</details>

#### ConcurrencyController - Basic

#### creates concurrency controller

- Verify: creates concurrency controller


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates concurrency controller")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(3)
expect controller.max_concurrent == 3
```

</details>

#### allows starting within limit

- Verify: allows starting within limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: allows starting within limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(2)
expect controller.try_start("task1")
expect controller.try_start("task2")
expect not controller.try_start("task3")
```

</details>

#### checks can start

- Verify: checks can start


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: checks can start")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(1)
expect controller.can_start()
controller.try_start("task")
expect not controller.can_start()
```

</details>

#### ConcurrencyController - Queue Management

#### queues tasks when at limit

- Verify: queues tasks when at limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: queues tasks when at limit")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(1)
controller.try_start("active")
controller.try_start("waiting")
expect controller.active_count == 1
expect controller.get_waiting_count() == 1
```

</details>

#### starts waiting task on completion

- Verify: starts waiting task on completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: starts waiting task on completion")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: tracks completed tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: tracks completed tasks")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(2)
controller.try_start("a")
controller.try_start("b")
controller.complete("a")
expect controller.get_completed_count() == 1
```

</details>

#### resets controller

- Verify: resets controller


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets controller")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val controller = ConcurrencyController.new(2)
controller.try_start("task")
controller.reset()
expect controller.active_count == 0
```

</details>

#### Debouncer - Basic

#### creates debouncer

- Verify: creates debouncer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates debouncer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val debouncer = Debouncer.new(100)
expect debouncer.delay_ms == 100
```

</details>

#### debounces rapid calls

- Verify: debounces rapid calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: debounces rapid calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: executes after delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: executes after delay")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val debouncer = Debouncer.new(100)
debouncer.call("value")
expect debouncer.has_pending()
debouncer.advance_time(150)
expect not debouncer.has_pending()
expect debouncer.get_execution_count() == 1
```

</details>

#### tracks execution count

- Verify: tracks execution count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: tracks execution count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val debouncer = Debouncer.new(50)
debouncer.call("a")
debouncer.advance_time(100)
debouncer.call("b")
debouncer.advance_time(100)
expect debouncer.get_execution_count() == 2
```

</details>

#### resets debouncer

- Verify: resets debouncer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets debouncer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val debouncer = Debouncer.new(100)
debouncer.call("value")
debouncer.advance_time(150)
debouncer.reset()
expect debouncer.get_execution_count() == 0
```

</details>

#### Throttler - Basic

#### creates throttler

- Verify: creates throttler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: creates throttler")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val throttler = Throttler.new(100)
expect throttler.interval_ms == 100
```

</details>

#### allows first call

- Verify: allows first call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: allows first call")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val throttler = Throttler.new(100)
expect throttler.call("first")
expect throttler.get_execution_count() == 1
```

</details>

#### throttles rapid calls

- Verify: throttles rapid calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: throttles rapid calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val throttler = Throttler.new(100)
expect throttler.call("first")
expect not throttler.call("second")
expect not throttler.call("third")
expect throttler.get_execution_count() == 1
```

</details>

#### allows call after interval

- Verify: allows call after interval


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: allows call after interval")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val throttler = Throttler.new(100)
throttler.call("first")
throttler.advance_time(150)
expect throttler.call("second")
expect throttler.get_execution_count() == 2
```

</details>

#### tracks dropped calls

- Verify: tracks dropped calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: tracks dropped calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val throttler = Throttler.new(100)
throttler.call("ok")
throttler.call("dropped1")
throttler.call("dropped2")
expect throttler.dropped_count == 2
```

</details>

#### resets throttler

- Verify: resets throttler


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: resets throttler")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: simulates API with rate limiting and retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: simulates API with rate limiting and retry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: tracks concurrent async operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: tracks concurrent async operations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles timeout with retry


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: handles timeout with retry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: priority scheduling with debounce


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE7-001
step("Verify: priority scheduling with debounce")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `619698f7db8aef5f6866d6f6b23f4861e152749eb52596aab5eacdeca87b4d51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `619698f7db8aef5f6866d6f6b23f4861e152749eb52596aab5eacdeca87b4d51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `619698f7db8aef5f6866d6f6b23f4861e152749eb52596aab5eacdeca87b4d51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/mock_phase7_spec.spl
mirror: doc/06_spec/01_unit/std/mock_phase7_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_phase7_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/mock_phase7_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_phase7_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
