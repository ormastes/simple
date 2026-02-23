# Mocking Guide

**Status:** Implemented (Phases 1-7 Complete)
**Library:** `std.testing.mock`

## Overview

The mock library provides comprehensive test doubles for verifying interactions with dependencies. It includes call tracking, verification, advanced analysis, trait-based mocking patterns, async mocking, and advanced scheduling.

## Quick Start

### Basic Mock

```simple
import std.testing.mock as mock

fn test_user_service():
    # Create a mock
    val save_mock = mock.create_mock("save_user")

    # Simulate function call
    save_mock.record_call(["user123", "Alice"])

    # Verify it was called
    expect save_mock.was_called()
    expect save_mock.call_count() == 1
    expect save_mock.was_called_with(["user123", "Alice"])
```

## Creating Mocks

### Method 1: Simple Creation

```simple
val mock = mock.create_mock("function_name")
```

### Method 2: With Return Values

```simple
val mock = mock.MockBuilder.new("get_user")
    .returns(["Alice", "Bob", "Charlie"])

# Get return values in sequence
match mock.next_return_value():
    Some(v): print v  # → "Alice"
    None: print "No more values"
```

### Method 3: Mock That Panics

```simple
val mock = mock.MockBuilder.new("fail_operation")
    .panics("Database connection failed")

# Mock is configured to panic when called
```

## Recording Calls

Track function invocations:

```simple
val mock = mock.create_mock("save_data")

# Record calls (arguments as strings)
mock.record_call(["arg1", "arg2"])
mock.record_call(["arg3"])

print mock.call_count()  # → 2
```

## Verification

### Was Called

```simple
if mock.was_called():
    print "Function was invoked"
```

### Called N Times

```simple
expect mock.was_called_n_times(3)
expect mock.call_count() == 3
```

### Called With Arguments

```simple
expect mock.was_called_with(["expected", "args"])
```

### Helper Functions

```simple
# Verify call count
expect mock.verify_called(mock, 5)

# Verify arguments
expect mock.verify_called_with(mock, ["user123"])
```

## Inspecting Calls

### Get Specific Call

```simple
match mock.get_call(0):  # First call (0-indexed)
    Some(call):
        print "Call #{call.call_number}"
        print "Args: {call.args}"
    None:
        print "No such call"
```

### Get Last Call

```simple
match mock.get_last_call():
    Some(call):
        print "Last call args: {call.args}"
    None:
        print "No calls recorded"
```

### Iterate All Calls

```simple
val mock = mock.create_mock("process")
mock.record_call(["data1"])
mock.record_call(["data2"])

for i in 0..mock.call_count():
    match mock.get_call(i):
        Some(call): print call.args
        None: break
```

## Mock Registry

Manage multiple mocks:

```simple
val registry = mock.MockRegistry.new()

# Register mocks
val save_mock = mock.create_mock("save")
val load_mock = mock.create_mock("load")

registry.register("save", save_mock)
registry.register("load", load_mock)

# Simulate operations
save_mock.record_call(["data"])
load_mock.record_call(["key"])

# Get summary
print registry.summary()

# Reset all mocks
registry.reset_all()
```

## Return Values

Simulate function returns:

```simple
val mock = mock.MockBuilder.new("fetch_data")
    .returns(["result1", "result2", "result3"])

# First call
match mock.next_return_value():
    Some(v): print v  # → "result1"
    None: pass

# Second call
match mock.next_return_value():
    Some(v): print v  # → "result2"
    None: pass

# When exhausted
match mock.next_return_value():
    None: print "No more values"
    Some(_): pass
```

## Resetting Mocks

Clear call history:

```simple
val mock = mock.create_mock("operation")

mock.record_call(["arg1"])
mock.record_call(["arg2"])
print mock.call_count()  # → 2

mock.reset()
print mock.call_count()  # → 0
```

## Real-World Examples

### Example 1: Testing a Service

```simple
import std.testing.mock as mock

fn test_user_service_saves_user():
    # Setup: Create mock repository
    val repo_mock = mock.create_mock("user_repository.save")

    # Execute: Call service (which uses repository)
    val service = UserService(repository: repo_mock)
    service.create_user("user123", "Alice")

    # Verify: Repository was called correctly
    expect repo_mock.was_called()
    expect repo_mock.was_called_with(["user123", "Alice"])
```

### Example 2: Testing API Client

```simple
fn test_api_client():
    val http_mock = mock.MockBuilder.new("http_client")
        .returns([
            '{"status": "ok"}',
            '{"status": "error"}'
        ])

    # First request succeeds
    match http_mock.next_return_value():
        Some(response):
            http_mock.record_call(["GET", "/api/users"])
            print "Response: {response}"
        None: fail "Expected response"

    # Verify
    expect http_mock.was_called_with(["GET", "/api/users"])
```

### Example 3: Dependency Injection

```simple
# Application code
class EmailService:
    mailer: MockFunction  # In real code, this would be a trait

    fn send_welcome(user_id: text):
        # Send email (using mock in tests)
        self.mailer.record_call(["welcome", user_id])
        # In real implementation, use mailer.next_return_value()

# Test code
fn test_email_service():
    val mailer_mock = mock.MockBuilder.new("mailer")
        .returns(["sent"])

    val service = EmailService(mailer: mailer_mock)
    service.send_welcome("user123")

    expect mailer_mock.was_called_with(["welcome", "user123"])
```

## Best Practices

### 1. Mock External Dependencies Only

❌ **Don't mock internal logic:**
```simple
# Bad: Mocking internal helper
val helper_mock = mock.create_mock("internal_helper")
```

✅ **Mock external dependencies:**
```simple
# Good: Mocking database, HTTP client, file system
val db_mock = mock.create_mock("database")
val http_mock = mock.create_mock("http_client")
```

### 2. Use Descriptive Names

❌ **Vague names:**
```simple
val m1 = mock.create_mock("fn")
```

✅ **Clear names:**
```simple
val user_repo_mock = mock.create_mock("user_repository.save")
val email_sender_mock = mock.create_mock("email_service.send")
```

### 3. Verify What Matters

❌ **Over-verification:**
```simple
# Don't verify every single call
expect mock.was_called()
expect mock.call_count() == 1
expect mock.was_called_n_times(1)
expect mock.was_called_with(args)
```

✅ **Verify behavior:**
```simple
# Verify the important interaction
expect mock.was_called_with(["user123", "Alice"])
```

### 4. Reset Between Tests

```simple
fn test_operation_a():
    val mock = mock.create_mock("op")
    mock.record_call(["a"])
    expect mock.call_count() == 1

fn test_operation_b():
    val mock = mock.create_mock("op")  # Fresh mock
    mock.record_call(["b"])
    expect mock.call_count() == 1
```

### 5. Use Registry for Complex Tests

```simple
fn test_complex_workflow():
    val registry = mock.MockRegistry.new()

    # Setup all mocks
    val db_mock = mock.create_mock("db")
    val cache_mock = mock.create_mock("cache")
    val email_mock = mock.create_mock("email")

    registry.register("db", db_mock)
    registry.register("cache", cache_mock)
    registry.register("email", email_mock)

    # ... test logic ...

    # Easy cleanup
    registry.reset_all()
}
```

## Limitations

### 1. No Automatic Mocking

Unlike languages with reflection, you must manually:
- Create mocks
- Call `record_call()` in your code
- Track return values

**Workaround:** Use dependency injection to pass mocks.

### 2. Arguments Are Strings

All arguments are stored as text:

```simple
# Must convert to strings
mock.record_call(["123", "true", "Alice"])

# Not type-safe
mock.was_called_with(["123"])  # OK
mock.was_called_with([123])    # Wrong type
```

**Future:** Will improve when trait objects are available.

### 3. No Trait Object Support

Cannot create mocks that implement traits directly.

**Workaround:** Explicitly pass mock to code under test.

### 4. Manual Call Recording

You must manually call `record_call()`:

```simple
# Your code must explicitly record calls
fn save_user(mock: MockFunction, user_id: text):
    mock.record_call([user_id])
    # ... actual logic ...
```

**Future:** Automatic call interception when language supports it.

## Troubleshooting

### Problem: Mock Not Recording Calls

**Symptoms:**
```simple
expect mock.was_called()  # Fails!
```

**Solutions:**
1. Ensure you're calling `mock.record_call()`
2. Check mock reference (ensure you're using the same instance)
3. Verify test execution order

### Problem: Wrong Call Count

**Symptoms:**
```simple
expect mock.call_count() == 1  # Fails, count is 3
```

**Solutions:**
1. Reset mock between tests
2. Check for extra calls
3. Use `mock.summary()` to see all calls

### Problem: Arguments Don't Match

**Symptoms:**
```simple
expect mock.was_called_with(["user123"])  # Fails
```

**Solutions:**
1. Print call history: `print mock.summary()`
2. Check argument order
3. Ensure arguments are strings
4. Use `get_last_call()` to inspect actual arguments

## Advanced Patterns

### Pattern 1: Spy (Partial Mock)

Track calls but use real implementation:

```simple
val spy = mock.create_mock("real_function")

fn call_with_spy(arg: text) -> text:
    spy.record_call([arg])
    real_function(arg)  # Call real implementation
```

### Pattern 2: Stub (Pre-configured Responses)

```simple
val stub = mock.MockBuilder.new("config_service")
    .returns([
        '{"api_key": "test123"}',
        '{"timeout": "30"}'
    ])

# Use stub in tests without assertions
```

### Pattern 3: Fake (Simple Implementation)

```simple
class FakeDatabase:
    calls: MockFunction
    data: Map<text, text>

    fn save(key: text, value: text):
        self.calls.record_call([key, value])
        self.data.insert(key, value)

    fn load(key: text) -> Option<text>:
        self.calls.record_call([key])
        self.data.get(key)
```

## Examples

See `simple/std_lib/examples/testing/mock_example.spl` for complete examples.

## API Reference

### Types

**`MockFunction`**
- `new(name)` - Create mock
- `record_call(args)` - Record invocation
- `set_return_values(values)` - Configure returns
- `next_return_value()` - Get next return
- `call_count()` - Get call count
- `was_called()` - Check if called
- `was_called_with(args)` - Check arguments
- `get_call(index)` - Get specific call
- `reset()` - Clear history

**`MockBuilder`**
- `new(name)` - Create builder
- `returns(values)` - Set return values
- `panics(message)` - Configure panic
- `build()` - Create mock

**`MockRegistry`**
- `new()` - Create registry
- `register(name, mock)` - Add mock
- `get(name)` - Retrieve mock
- `reset_all()` - Reset all mocks
- `summary()` - Get summary

### Functions

- `create_mock(name)` - Create simple mock
- `verify_called(mock, times)` - Verify call count
- `verify_called_with(mock, args)` - Verify arguments

---

## Phase 4: Advanced Patterns

### Conditional Returns

Return different values based on arguments:

```simple
val cond = mock.ConditionalReturns.new()
cond.add_condition(\args: args[0] == "admin", "admin_data")
cond.add_condition(\args: args[0] == "user", "user_data")
cond.set_default("guest_data")

val result = cond.evaluate(["admin"])  # → "admin_data"
```

### Behavior Sequences (State Machines)

Simulate stateful behavior:

```simple
val seq = mock.BehaviorSequence.new("disconnected")
seq.add_state("disconnected", "connecting...", Some("connecting"))
seq.add_state("connecting", "connected!", Some("connected"))
seq.add_state("connected", "ready", nil)

val r1 = seq.transition()  # → "connecting..."
val r2 = seq.transition()  # → "connected!"
val r3 = seq.transition()  # → "ready"
```

### Mock Snapshots

Capture mock state for comparison:

```simple
val mock = mock.create_mock("service")
mock.record_call(["data"])

val snapshot = mock.MockSnapshot.from_mock(mock)
print snapshot.call_count      # → 1
print snapshot.expectations_met  # → true
```

### Mock Composition

Manage related mocks together:

```simple
val comp = mock.MockComposition.new()
comp.add_mock(db_mock)
comp.add_mock(cache_mock)
comp.add_mock(api_mock)

# Verify all mocks
if comp.verify_all():
    print "All expectations met"

# Get statistics
print comp.get_total_calls()
comp.reset_all()
```

---

## Phase 5: Trait-Based Mocking

### Fluent Expectations

Chainable when/returns API:

```simple
val mockfn = mock.MockFunction.new("api")
val fluent = mock.FluentExpectation.new(mockfn)
fluent.when_called_with(["GET", "/users"]).returns("user_data")
```

### When Builder

Predicate-based conditions:

```simple
val when_builder = mock.WhenBuilder.new(mockfn)
when_builder
    .when(\args: args[0] == "valid")
    .returns("OK")
```

### Protocol Mock

Simulate trait-like interfaces without trait objects:

```simple
val proto = mock.ProtocolMock.new()
proto.mock_method("authenticate", ["user", "pass"], "token_123")
proto.mock_method("authorize", ["token"], "granted")

val token = proto.record_method_call("authenticate", ["user", "pass"])
expect token == "token_123"
expect proto.verify_method_called("authenticate")
```

### Auto Mock

Automatic mock generation:

```simple
val auto = mock.AutoMock.new("Database")
auto.add_property("connection_string")
auto.setup_method("connect", ["host"], "connected")
auto.setup_method("query", ["sql"], "rows")

expect auto.call_method("connect", ["host"]) == "connected"
print auto.summary()
```

---

## Phase 6: Async/Await Mocking

### AsyncMock

Mock asynchronous operations with delay simulation:

```simple
val async_mock = mock.AsyncMock.new("api_call")
async_mock.set_delay(100)  # Simulate 100ms latency
async_mock.set_return_values(["response1", "response2"])

val result = async_mock.record_async_call(["request"])
expect result == "response1"
expect async_mock.get_total_delay() == 100
```

### Error Simulation

```simple
val failing_mock = mock.AsyncMock.new("failing_api")
failing_mock.set_error("Network timeout")

failing_mock.record_async_call(["request"])
val errors = failing_mock.get_calls_with_errors()
expect errors.len() == 1
```

### Promise Sequences

Sequential async returns with timing:

```simple
val seq = mock.PromiseSequence.new()
seq.add_promise("success", 50)      # 50ms delay
seq.add_promise_error("timeout", 100)  # Error after 100ms
seq.add_promise("retry_success", 25)

while seq.remaining() > 0:
    match seq.next_promise():
        Some(p):
            if p.is_error:
                print "Error: {p.value}"
            else:
                print "Result: {p.value} ({p.delay_ms}ms)"
        nil: break
```

### AsyncSpy

Track async calls with timing statistics:

```simple
val spy = mock.AsyncSpy.new("performance_spy")
spy.record_async_call("fetch", ["url1"], 45)
spy.record_async_call("fetch", ["url2"], 55)
spy.record_async_call("fetch", ["url3"], 50)

val stats = spy.get_call_timing_stats("fetch")
expect stats.min_ms == 45
expect stats.max_ms == 55
expect stats.avg_ms == 50
expect stats.count == 3
```

### AsyncProtocolMock

Async trait simulation:

```simple
val proto = mock.AsyncProtocolMock.new()
proto.mock_async_method("fetchUser", ["id"], 50, "user_data")
proto.mock_async_method("saveUser", ["data"], 100, "saved")

val result = proto.record_async_method_call("fetchUser", ["id"])
expect result == "user_data"
expect proto.get_total_delay() == 50
```

### AsyncMockComposition

Orchestrate multiple async mocks:

```simple
val comp = mock.AsyncMockComposition.new()
val auth = mock.AsyncMock.new("auth")
val db = mock.AsyncMock.new("database")

auth.set_delay(50)
db.set_delay(100)
auth.set_return_values(["token"])
db.set_return_values(["data"])

comp.add_async_mock("auth", auth)
comp.add_async_mock("db", db)

auth.record_async_call([])
db.record_async_call([])

expect comp.verify_all_called()
expect comp.get_total_delay() == 150
```

### Timing Matchers

Assert on execution timing:

```simple
val matcher = mock.AsyncTimingMatcher.within_ms(100)
expect matcher.matches(75)  # true
expect matcher.matches(150) # false

val range_matcher = mock.AsyncTimingMatcher.between_ms(50, 100)
expect range_matcher.matches(75)  # true

# Verify mock timing
expect mock.verify_async_timing(async_mock, matcher)
```

---

## Phase 7: Advanced Scheduling

### Task Scheduler

Priority-based task execution:

```simple
val scheduler = mock.TaskScheduler.new()

# Schedule tasks with priorities
val id1 = scheduler.schedule("critical", mock.TaskPriority.Critical, 10)
val id2 = scheduler.schedule("normal", mock.TaskPriority.Normal, 10)
val id3 = scheduler.schedule("high", mock.TaskPriority.High, 10)

# Execute in priority order
scheduler.execute_all()
expect scheduler.verify_execution_order([id1, id3, id2])

# Convenience methods
scheduler.schedule_immediate("urgent")      # High priority, no delay
scheduler.schedule_delayed("later", 500)    # Normal priority
scheduler.schedule_background("bg", 1000)   # Background priority
```

### Retry Policy

Configurable retry with backoff strategies:

```simple
# Exponential backoff
val retry = mock.RetryPolicy.with_exponential_backoff(5, 100)
# Delays: 100ms, 200ms, 400ms, 800ms, 1600ms

# Linear backoff
val linear = mock.RetryPolicy.with_linear_backoff(5, 100)
# Delays: 100ms, 200ms, 300ms, 400ms, 500ms

# Track attempts
while retry.should_retry():
    val success = attempt_operation()
    if success:
        retry.record_attempt(true, nil)
    else:
        retry.record_attempt(false, Some("Failed"))

print retry.get_attempt_count()
print retry.get_total_delay()
print retry.was_successful()
```

### Rate Limiter

Simulate API rate limiting:

```simple
val limiter = mock.RateLimiter.per_second(10)  # 10 requests/second

# Try to make requests
if limiter.try_acquire():
    print "Request allowed"
else:
    print "Rate limited, wait {limiter.get_wait_time()}ms"

# Advance time and cleanup
limiter.advance_time(1000)
expect limiter.can_proceed()

print limiter.get_remaining_requests()
```

### Timeout Controller

Handle async operation timeouts:

```simple
val timeout = mock.TimeoutController.new(5000)  # 5 second timeout
timeout.start()

# Simulate work
timeout.advance(3000)
print timeout.remaining_time()  # → 2000

# Complete or timeout
val result = timeout.complete()
if result.completed:
    print "Finished in {result.duration_ms}ms"
else:
    print "Operation timed out"
```

### Execution Order Tracker

Verify concurrent execution order:

```simple
val tracker = mock.ExecutionOrderTracker.new()

tracker.record_start("task1")
tracker.advance_time(10)
tracker.record_start("task2")
tracker.advance_time(50)
tracker.record_end("task1")
tracker.advance_time(50)
tracker.record_end("task2")

# Verify ordering
expect tracker.verify_started_before("task1", "task2")
expect tracker.verify_completed_before("task1", "task2")

# Get concurrent tasks at a point in time
val concurrent = tracker.get_concurrent_at(30)
expect concurrent.len() == 2
```

### Concurrency Controller

Control concurrent execution limits:

```simple
val controller = mock.ConcurrencyController.new(2)  # Max 2 concurrent

expect controller.try_start("task1")  # true
expect controller.try_start("task2")  # true
expect controller.try_start("task3")  # false (queued)

expect controller.get_active_count() == 2
expect controller.get_waiting_count() == 1

# Complete a task, queued task starts automatically
controller.complete("task1")
expect controller.get_active_tasks() == ["task2", "task3"]
```

### Debouncer

Debounce rapid calls:

```simple
val debouncer = mock.Debouncer.new(100)  # 100ms debounce

debouncer.call("first")
debouncer.advance_time(50)
debouncer.call("second")   # Resets timer
debouncer.advance_time(50)
debouncer.call("third")    # Resets timer
debouncer.advance_time(150)

# Only last value executed
val executed = debouncer.get_executed_values()
expect executed.len() == 1
expect executed[0] == "third"
```

### Throttler

Throttle execution rate:

```simple
val throttler = mock.Throttler.new(100)  # Allow once per 100ms

expect throttler.call("first")   # true - allowed
expect throttler.call("second")  # false - dropped
expect throttler.call("third")   # false - dropped

throttler.advance_time(150)
expect throttler.call("fourth")  # true - allowed

print throttler.get_execution_count()  # → 2
print throttler.get_dropped_count()    # → 2
```

---

## Complete Phase Summary

| Phase | Features | Status |
|-------|----------|--------|
| 1 | Call tracking, MockFunction, MockBuilder, MockRegistry | ✅ Complete |
| 2 | Verification system, Matcher, Expectation | ✅ Complete |
| 3 | CallAnalyzer, SequentialReturns, Spy | ✅ Complete |
| 4 | ConditionalReturns, BehaviorSequence, MockSnapshot, MockComposition | ✅ Complete |
| 5 | FluentExpectation, WhenBuilder, ProtocolMock, AutoMock | ✅ Complete |
| 6 | AsyncMock, PromiseSequence, AsyncSpy, AsyncProtocolMock, AsyncTimingMatcher | ✅ Complete |
| 7 | TaskScheduler, RetryPolicy, RateLimiter, TimeoutController, Debouncer, Throttler | ✅ Complete |

**Total:** ~1,900 LOC implementation, 70+ APIs, 300+ test cases
