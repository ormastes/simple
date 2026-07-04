# mock_spec

> Mock Library Specification

<!-- sdn-diagram:id=mock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/std/testing/mock_spec.spl` |
| Updated | 2026-06-01 |
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

1. expect m call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MockFunction__new("save_user")
expect m.call_count() == 0
```

</details>

#### initializes empty call history

1. expect m was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MockFunction__new("test_fn")
expect m.was_called() == false
```

</details>

#### Call Recording

#### records function calls

1. mfn record call
2. expect mfn was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("fetch_data")
mfn.record_call(["user_id", "123"])
expect mfn.was_called() == true
```

</details>

#### tracks call count

1. mfn record call
2. mfn record call
3. mfn record call
4. expect mfn call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("process")
mfn.record_call([])
mfn.record_call([])
mfn.record_call([])
expect mfn.call_count() == 3
```

</details>

#### tracks multiple calls with different arguments

1. mfn record call
2. mfn record call
3. expect mfn call count
4. expect mfn was called with
5. expect mfn was called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn record call
2. expect mfn was called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("update_user")
mfn.record_call(["user_123", "Alice"])
expect mfn.was_called_with(["user_123", "Alice"])
```

</details>

#### returns false for unmatched arguments

1. mfn record call
2. expect mfn was called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("delete_record")
mfn.record_call(["record_456"])
expect mfn.was_called_with(["record_123"]) == false
```

</details>

#### finds argument match in multiple calls

1. mfn record call
2. mfn record call
3. mfn record call
4. expect mfn was called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("log")
mfn.record_call(["info", "Application started"])
mfn.record_call(["error", "Connection failed"])
mfn.record_call(["info", "Application stopped"])
expect mfn.was_called_with(["error", "Connection failed"])
```

</details>

#### Call Inspection

#### retrieves specific call by index

1. mfn record call
2. mfn record call
3. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn record call
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("my_fn")
mfn.record_call(["arg"])
val result = mfn.get_call(5)
match result:
    Some(_): expect false
    nil: expect true
```

</details>

#### retrieves last call

1. mfn record call
2. mfn record call
3. mfn record call
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn record call
2. mfn record call
3. expect mfn was called n times


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("handler")
mfn.record_call([])
mfn.record_call([])
expect mfn.was_called_n_times(2)
```

</details>

#### returns false for mismatched count

1. mfn record call
2. expect mfn was called n times


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("processor")
mfn.record_call([])
expect mfn.was_called_n_times(5) == false
```

</details>

#### Return Values

#### provides sequential return values

1. mfn set return values
2. expect r1 == Some
3. expect r2 == Some
4. expect r3 == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn set return values
2. mfn next return value
3. mfn next return value
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn set return values
2. mfn next return value
3. mfn reset
4. expect after reset == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mfn record call
2. mfn record call
3. mfn reset
4. expect mfn call count
5. expect mfn was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("clearable")
mfn.record_call(["arg1"])
mfn.record_call(["arg2"])

mfn.reset()
expect mfn.call_count() == 0
expect mfn.was_called() == false
```

</details>

#### clears return value state

1. mfn set return values
2. mfn next return value
3. mfn reset
4. expect value == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect builder mock call count
2. expect value == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder_mock = MockBuilder__new("get_user").returns(["user_data"])
expect builder_mock.call_count() == 0
val value = builder_mock.next_return_value()
expect value == Some("user_data")
```

</details>

#### builds mock that panics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panic_mock = MockBuilder__new("fail_op").panics("Error occurred")
expect panic_mock.should_panic == true
expect panic_mock.panic_message == "Error occurred"
```

</details>

#### builds basic mock

1. expect basic mock call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val basic_mock = MockBuilder__new("simple").build()
expect basic_mock.call_count() == 0
```

</details>

#### MockRegistry

#### registers and retrieves mocks

1. registry register
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = MockRegistry__new()
val result = registry.get("nonexistent")
match result:
    Some(_): expect false
    nil: expect true
```

</details>

#### resets all mocks

1. mock1 record call
2. mock2 record call
3. registry register
4. registry register
5. registry reset all
6. expect mock1 was called
7. expect mock2 was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect mfn was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = create_mock("fetch_user")
expect mfn.was_called() == false
```

</details>

#### verifies call count with helper

1. mfn record call
2. mfn record call
3. expect verify called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = create_mock("process")
mfn.record_call(["item1"])
mfn.record_call(["item2"])
expect verify_called(mfn, 2)
```

</details>

#### verifies arguments with helper

1. mfn record call
2. expect verify called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = create_mock("save")
mfn.record_call(["id_123", "data"])
expect verify_called_with(mfn, ["id_123", "data"])
```

</details>

#### Summary Output

#### generates summary for uncalled mock

1. expect summary contains
2. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mfn = MockFunction__new("unused")
val summary = mfn.summary()
expect summary.contains("unused")
expect summary.contains("not called")
```

</details>

#### generates summary for called mock

1. mfn record call
2. expect summary contains
3. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# trait Database:
#     fn get_user(id: i32) -> Option<User>
#
# val mock_db = mock!(Database)
# expect mock_db.is_some()
expect true
```

</details>

#### allows method chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val mock = mock!(Service)
# mocking.when("fetch").returns_once(Some(data))
#
# expect mocking.fetch().is_some()
# expect mocking.fetch().is_none()  # Second call returns None
expect true
```

</details>

#### supports error results for error simulation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val mock = mock!(Service)
# mocking.expect("send").once()
#
# mocking.reset()
# expect mocking.expectations.is_empty()
expect true
```

</details>

#### clears stubs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
