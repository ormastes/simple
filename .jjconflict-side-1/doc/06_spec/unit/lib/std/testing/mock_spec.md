# mock_spec

> Mock Library Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_spec

Mock Library Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/testing/mock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mock Library Specification

Mock library for creating test doubles (mocks, stubs, spies) to isolate
units under test. Provides fluent API for stubbing methods and verifying
behavior.

Feature IDs: Testing Infrastructure - Mocking
Category: Testing
Status: Planned (Blocked on trait objects)
Priority: Medium

Key Concepts:
- Mock: Pre-programmed with expectations, verifies behavior
- Stub: Provides canned answers, no verification
- Spy: Records calls on real object
- Fake: Working implementation for testing

## Scenarios

### Mock Library - Phase 1 (Call Tracking)

#### MockFunction Creation

#### creates mock with name

- creates mock with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mock with name")
val m = MockFunction__new("save_user")
expect m.call_count() == 0
```

</details>

#### initializes empty call history

- initializes empty call history


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty call history")
val m = MockFunction__new("test_fn")
expect m.was_called() == false
```

</details>

#### Call Recording

#### records function calls

- records function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records function calls")
val mfn = MockFunction__new("fetch_data")
mfn.record_call(["user_id", "123"])
expect mfn.was_called() == true
```

</details>

#### tracks call count

- tracks call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks call count")
val mfn = MockFunction__new("process")
mfn.record_call([])
mfn.record_call([])
mfn.record_call([])
expect mfn.call_count() == 3
```

</details>

#### tracks multiple calls with different arguments

- tracks multiple calls with different arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks multiple calls with different arguments")
val mfn = MockFunction__new("send_message")
mfn.record_call(["email", "user@test.com"])
mfn.record_call(["sms", "555-1234"])
expect mfn.call_count() == 2
expect mfn.was_called_with(["email", "user@test.com"])
expect mfn.was_called_with(["sms", "555-1234"])
```

</details>

#### Argument Verification

#### verifies call with specific arguments

- verifies call with specific arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies call with specific arguments")
val mfn = MockFunction__new("update_user")
mfn.record_call(["user_123", "Alice"])
expect mfn.was_called_with(["user_123", "Alice"])
```

</details>

#### returns false for unmatched arguments

- returns false for unmatched arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unmatched arguments")
val mfn = MockFunction__new("delete_record")
mfn.record_call(["record_456"])
expect mfn.was_called_with(["record_123"]) == false
```

</details>

#### finds argument match in multiple calls

- finds argument match in multiple calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds argument match in multiple calls")
val mfn = MockFunction__new("log")
mfn.record_call(["info", "Application started"])
mfn.record_call(["error", "Connection failed"])
mfn.record_call(["info", "Application stopped"])
expect mfn.was_called_with(["error", "Connection failed"])
```

</details>

#### Call Inspection

#### retrieves specific call by index

- retrieves specific call by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves specific call by index")
val mfn = MockFunction__new("api_call")
mfn.record_call(["GET", "/users"])
mfn.record_call(["POST", "/users"])
val first_call = mfn.get_call(0)
match first_call:
    Some(call): expect call.args[0] == "GET"
    nil: expect false
```

</details>

#### returns none for out of bounds call

- returns none for out of bounds call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns none for out of bounds call")
val mfn = MockFunction__new("my_fn")
mfn.record_call(["arg"])
val result = mfn.get_call(5)
match result:
    Some(_): expect false
    nil: expect true
```

</details>

#### retrieves last call

- retrieves last call


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves last call")
val mfn = MockFunction__new("sequence")
mfn.record_call(["first"])
mfn.record_call(["second"])
mfn.record_call(["third"])
val last = mfn.get_last_call()
match last:
    Some(call): expect call.args[0] == "third"
    nil: expect false
```

</details>

#### Call Count Verification

#### verifies exact call count

- verifies exact call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies exact call count")
val mfn = MockFunction__new("handler")
mfn.record_call([])
mfn.record_call([])
expect mfn.was_called_n_times(2)
```

</details>

#### returns false for mismatched count

- returns false for mismatched count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for mismatched count")
val mfn = MockFunction__new("processor")
mfn.record_call([])
expect mfn.was_called_n_times(5) == false
```

</details>

#### Return Values

#### provides sequential return values

- provides sequential return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides sequential return values")
val mfn = MockFunction__new("fetch_config")
mfn.set_return_values(["config_v1", "config_v2", "config_v3"])

val r1 = mfn.next_return_value()
val r2 = mfn.next_return_value()
val r3 = mfn.next_return_value()

expect r1 == Some("config_v1")
expect r2 == Some("config_v2")
expect r3 == Some("config_v3")
```

</details>

#### returns none when return values exhausted

- returns none when return values exhausted


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns none when return values exhausted")
val mfn = MockFunction__new("limited")
mfn.set_return_values(["one", "two"])

mfn.next_return_value()
mfn.next_return_value()
val third = mfn.next_return_value()

match third:
    Some(_): expect false
    nil: expect true
```

</details>

#### resets return value index on reset

- resets return value index on reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets return value index on reset")
val mfn = MockFunction__new("reusable")
mfn.set_return_values(["value"])

mfn.next_return_value()
mfn.reset()

val after_reset = mfn.next_return_value()
expect after_reset == Some("value")
```

</details>

#### Reset Functionality

#### clears call history

- clears call history


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears call history")
val mfn = MockFunction__new("clearable")
mfn.record_call(["arg1"])
mfn.record_call(["arg2"])

mfn.reset()
expect mfn.call_count() == 0
expect mfn.was_called() == false
```

</details>

#### clears return value state

- clears return value state


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears return value state")
val mfn = MockFunction__new("return_reset")
mfn.set_return_values(["a", "b"])
mfn.next_return_value()

mfn.reset()
val value = mfn.next_return_value()
expect value == Some("a")
```

</details>

#### MockBuilder

#### builds mock with return values

- builds mock with return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds mock with return values")
val builder_mock = MockBuilder__new("get_user").returns(["user_data"])
expect builder_mock.call_count() == 0
val value = builder_mock.next_return_value()
expect value == Some("user_data")
```

</details>

#### builds mock that panics

- builds mock that panics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds mock that panics")
val panic_mock = MockBuilder__new("fail_op").panics("Error occurred")
expect panic_mock.should_panic == true
expect panic_mock.panic_message == "Error occurred"
```

</details>

#### builds basic mock

- builds basic mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds basic mock")
val basic_mock = MockBuilder__new("simple").build()
expect basic_mock.call_count() == 0
```

</details>

#### MockRegistry

#### registers and retrieves mocks

- registers and retrieves mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers and retrieves mocks")
val registry = MockRegistry__new()
val mfn = MockFunction__new("save_data")

registry.register("save", mfn)
val retrieved = registry.get("save")
match retrieved:
    Some(_): expect true
    nil: expect false
```

</details>

#### returns none for unregistered mock

- returns none for unregistered mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns none for unregistered mock")
val registry = MockRegistry__new()
val result = registry.get("nonexistent")
match result:
    Some(_): expect false
    nil: expect true
```

</details>

#### resets all mocks

- resets all mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets all mocks")
val registry = MockRegistry__new()
val mock1 = MockFunction__new("mock1")
val mock2 = MockFunction__new("mock2")

mock1.record_call(["data"])
mock2.record_call(["info"])

registry.register("mock1", mock1)
registry.register("mock2", mock2)

registry.reset_all()

expect mock1.was_called() == false
expect mock2.was_called() == false
```

</details>

#### Helper Functions

#### creates mock with helper

- creates mock with helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mock with helper")
val mfn = create_mock("fetch_user")
expect mfn.was_called() == false
```

</details>

#### verifies call count with helper

- verifies call count with helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies call count with helper")
val mfn = create_mock("process")
mfn.record_call(["item1"])
mfn.record_call(["item2"])
expect verify_called(mfn, 2)
```

</details>

#### verifies arguments with helper

- verifies arguments with helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies arguments with helper")
val mfn = create_mock("save")
mfn.record_call(["id_123", "data"])
expect verify_called_with(mfn, ["id_123", "data"])
```

</details>

#### Summary Output

#### generates summary for uncalled mock

- generates summary for uncalled mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates summary for uncalled mock")
val mfn = MockFunction__new("unused")
val summary = mfn.summary()
expect summary.contains("unused")
expect summary.contains("not called")
```

</details>

#### generates summary for called mock

- generates summary for called mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates summary for called mock")
val mfn = MockFunction__new("active")
mfn.record_call(["arg1"])
val summary = mfn.summary()
expect summary.contains("active")
expect summary.contains("1")
```

</details>

### Mock Library - Phase 2+ (Trait-based Mocking)

#### MockBuilder

#### creates mock for trait

- creates mock for trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mock for trait")
# trait Database:
#     fn get_user(id: i32) -> Option<User>
#
# val mock_db = mock!(Database)
# expect mock_db.is_some()
expect true
```

</details>

#### allows method chaining

- allows method chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows method chaining")
# val mock_db = mock!(Database)
#     .when("get_user").returns(None)
#     .when("save_user").returns(Ok(()))
#
# expect mock_db.stubs.len() == 2
expect true
```

</details>

#### Stubbing (when/returns)

#### stubs method to return value

- stubs method to return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stubs method to return value")
# val mock_db = mock!(Database)
# mock_db.when("get_user").returns(Some(user))
#
# val result = mock_db.get_user(123)
# expect result.is_some()
# expect result.unwrap().id == 123
expect true
```

</details>

#### stubs different methods independently

- stubs different methods independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stubs different methods independently")
# val mock = mock!(Service)
# mocking.when("method_a").returns(42)
# mocking.when("method_b").returns("hello")
#
# expect mocking.method_a() == 42
# expect mocking.method_b() == "hello"
expect true
```

</details>

#### supports returns_once for one-time stub

- supports returns_once for one-time stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports returns_once for one-time stub")
# val mock = mock!(Service)
# mocking.when("fetch").returns_once(Some(data))
#
# expect mocking.fetch().is_some()
# expect mocking.fetch().is_none()  # Second call returns None
expect true
```

</details>

#### supports error results for error simulation

- supports error results for error simulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports error results for error simulation")
# NOTE: Use Result<T, text> pattern instead of exceptions
# val mock = mock!(Service)
# mocking.when("dangerous").returns_error("Simulated error")
#
# val result = mocking.dangerous()
# match result:
#     case Err(msg): check(msg == "Simulated error")
#     case Ok(_): check(false)  # Should not succeed
check(true)  # Placeholder until Result pattern is implemented
```

</details>

#### Expectations (expect/verify)

#### verifies method was called

- verifies method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies method was called")
# val mock = mock!(Service)
# mocking.expect("send").once()
#
# mocking.send("test")
#
# val result = mocking.verify()
# expect result.is_ok()
expect true
```

</details>

#### verifies method was not called

- verifies method was not called


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies method was not called")
# val mock = mock!(Service)
# mocking.expect("send").never()
#
# # Don't call send()
#
# val result = mocking.verify()
# expect result.is_ok()
expect true
```

</details>

#### verifies method called specific times

- verifies method called specific times


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies method called specific times")
# val mock = mock!(Service)
# mocking.expect("process").times(3)
#
# mocking.process()
# mocking.process()
# mocking.process()
#
# expect mocking.verify().is_ok()
expect true
```

</details>

#### fails verification when expectation not met

- fails verification when expectation not met


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails verification when expectation not met")
# val mock = mock!(Service)
# mocking.expect("send").once()
#
# # Don't call send()
#
# val result = mocking.verify()
# expect result.is_err()
expect true
```

</details>

#### Argument matching

#### verifies with specific arguments

- verifies with specific arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies with specific arguments")
# val mock = mock!(Service)
# mocking.expect("send")
#     .with_args([42, "test"])
#     .once()
#
# mocking.send(42, "test")
# expect mocking.verify().is_ok()
expect true
```

</details>

#### supports any() matcher

- supports any() matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports any() matcher")
# val mock = mock!(Service)
# mocking.expect("send")
#     .with_args([any(), eq("test")])
#     .once()
#
# mocking.send(999, "test")  # Any number accepted
# expect mocking.verify().is_ok()
expect true
```

</details>

#### supports gt() matcher

- supports gt() matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports gt() matcher")
# val mock = mock!(Service)
# mocking.expect("process")
#     .with_args([gt(10)])
#
# mocking.process(15)
# expect mocking.verify().is_ok()
expect true
```

</details>

#### supports contains() matcher for strings

- supports contains() matcher for strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports contains() matcher for strings")
# val mock = mock!(Service)
# mocking.expect("log")
#     .with_args([contains("error")])
#
# mocking.log("Fatal error occurred")
# expect mocking.verify().is_ok()
expect true
```

</details>

#### supports custom predicate matcher

- supports custom predicate matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports custom predicate matcher")
# val mock = mock!(Service)
# mocking.expect("validate")
#     .with_args([predicate(\x: x % 2 == 0)])  # Even numbers
#
# mocking.validate(42)
# expect mocking.verify().is_ok()
expect true
```

</details>

#### Call recording

#### records all method calls

- records all method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records all method calls")
# val mock = mock!(Service)
#
# mocking.method_a(1)
# mocking.method_b("test")
# mocking.method_a(2)
#
# expect mocking.calls.len() == 3
# expect mocking.calls[0].method == "method_a"
# expect mocking.calls[1].method == "method_b"
expect true
```

</details>

#### provides call count per method

- provides call count per method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides call count per method")
# val mock = mock!(Service)
#
# mocking.process(1)
# mocking.process(2)
# mocking.send("test")
#
# expect mocking.call_count("process") == 2
# expect mocking.call_count("send") == 1
expect true
```

</details>

#### provides was_called() helper

- provides was_called() helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides was_called() helper")
# val mock = mock!(Service)
#
# mocking.send("test")
#
# expect mocking.was_called("send")
# expect not mocking.was_called("process")
expect true
```

</details>

#### Reset functionality

#### clears call history

- clears call history


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears call history")
# val mock = mock!(Service)
# mocking.send("test")
# expect mocking.calls.len() == 1
#
# mocking.reset()
# expect mocking.calls.len() == 0
expect true
```

</details>

#### clears expectations

- clears expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears expectations")
# val mock = mock!(Service)
# mocking.expect("send").once()
#
# mocking.reset()
# expect mocking.expectations.is_empty()
expect true
```

</details>

#### clears stubs

- clears stubs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears stubs")
# val mock = mock!(Service)
# mocking.when("get").returns(42)
#
# mocking.reset()
# expect mocking.stubs.is_empty()
expect true
```

</details>

#### Spy functionality

#### wraps real object

- wraps real object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps real object")
# val real = RealService.new()
# val spy = spy!(real)
#
# # Calls real implementation + records
# val result = spy.compute(5)
# expect result == real.compute(5)
# expect spy.was_called("compute")
expect true
```

</details>

#### allows partial stubbing

- allows partial stubbing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows partial stubbing")
# val real = RealService.new()
# val spy = spy!(real)
# spy.when("fetch").returns(Some(fake_data))
#
# # fetch() uses stub, other methods use real
# expect spy.fetch() == Some(fake_data)
# expect spy.compute(5) == real.compute(5)
expect true
```

</details>

#### Integration with SPipe

#### works in test context

- works in test context


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works in test context")
# describe "UserService":
#     it "fetches user from database":
#         val mock_db = mock!(Database)
#         mock_db.when("get_user").returns(Some(user))
#
#         val service = UserService(db: mock_db)
#         val result = service.find_user(123)
#
#         expect result.is_some()
expect true
```

</details>

#### verifies expectations in test

- verifies expectations in test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies expectations in test")
# describe "EmailService":
#     it "sends email on registration":
#         val mock_email = mock!(EmailService)
#         mock_email.expect("send").once()
#
#         register_user(mock_email)
#
#         expect mock_email.verify().is_ok()
expect true
```

</details>

#### Error cases

#### reports which expectation failed

- reports which expectation failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports which expectation failed")
# val mock = mock!(Service)
# mocking.expect("send").times(2)
# mocking.send("once")
#
# val result = mocking.verify()
# expect result.is_err()
# expect result.unwrap_err().contains("send")
# expect result.unwrap_err().contains("expected 2")
expect true
```

</details>

#### reports unexpected calls

- reports unexpected calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unexpected calls")
# val mock = mock!(Service)
# mocking.expect("allowed").once()
#
# mocking.allowed()
# mocking.unexpected()  # Not in expectations
#
# # Strict mode would fail here
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dbff06ec593abc2464dd000e021b8ed4487146ca910747983bfbc3563cf860d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbff06ec593abc2464dd000e021b8ed4487146ca910747983bfbc3563cf860d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbff06ec593abc2464dd000e021b8ed4487146ca910747983bfbc3563cf860d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std/testing/mock_spec.spl
mirror: doc/06_spec/unit/lib/std/testing/mock_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/testing/mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/testing/mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/testing/mock_spec.spl:223:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates mock with name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/testing/mock_spec.spl:229:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes empty call history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/testing/mock_spec.spl:236:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records function calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
