# Mock Phase6 Specification

> Tests covering Mock Library - Phase 6 (Async/Await Mocking).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Phase6 Specification

## Scenarios

### Mock Library - Phase 6 (Async/Await Mocking)

#### AsyncCallRecord

#### stores async call with timing info

- stores async call with timing info


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores async call with timing info")
val record = AsyncCallRecord(
    args: ["data"],
    timestamp: 100,
    call_number: 0,
    completion_time: 50,
    result: Some("success"),
    error: nil,
    delay_ms: 50
)
expect record.args[0] == "data"
expect record.delay_ms == 50
expect record.result.is_some()
```

</details>

#### stores error information

- stores error information


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores error information")
val record = AsyncCallRecord(
    args: ["fail"],
    timestamp: 100,
    call_number: 0,
    completion_time: 10,
    result: nil,
    error: Some("timeout"),
    delay_ms: 10
)
expect record.error.is_some()
expect record.result.is_none()
```

</details>

#### AsyncMock - Basic

#### creates async mock

- creates async mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates async mock")
val async_mock = AsyncMock.new("api_call")
expect async_mock.name == "api_call"
expect async_mock.call_count() == 0
```

</details>

#### sets delay for async mock

- sets delay for async mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets delay for async mock")
val async_mock = AsyncMock.new("fetch")
async_mock.set_delay(100)
expect async_mock.default_delay_ms == 100
```

</details>

#### sets return values

- sets return values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets return values")
val async_mock = AsyncMock.new("query")
async_mock.set_return_values(["result1", "result2"])
expect async_mock.return_values.len() == 2
```

</details>

#### records async call

- records async call


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records async call")
val async_mock = AsyncMock.new("service")
async_mock.set_return_values(["response"])
val result = async_mock.record_async_call(["request"])
expect result == "response"
expect async_mock.call_count() == 1
```

</details>

#### AsyncMock - Verification

#### verifies was called

- verifies was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies was called")
val async_mock = AsyncMock.new("handler")
expect not async_mock.was_called()
async_mock.set_return_values(["ok"])
async_mock.record_async_call([])
expect async_mock.was_called()
```

</details>

#### verifies was called with args

- verifies was called with args


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies was called with args")
val async_mock = AsyncMock.new("process")
async_mock.set_return_values(["done"])
async_mock.record_async_call(["arg1", "arg2"])
expect async_mock.was_called_with(["arg1", "arg2"])
expect not async_mock.was_called_with(["other"])
```

</details>

#### gets specific call

- gets specific call


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets specific call")
val async_mock = AsyncMock.new("db")
async_mock.set_return_values(["r1", "r2", "r3"])
async_mock.record_async_call(["a"])
async_mock.record_async_call(["b"])
async_mock.record_async_call(["c"])
match async_mock.get_call(1):
    Some(call): expect call.args[0] == "b"
    nil: fail "Expected call at index 1"
```

</details>

#### gets last call

- gets last call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets last call")
val async_mock = AsyncMock.new("event")
async_mock.set_return_values(["e1", "e2"])
async_mock.record_async_call(["first"])
async_mock.record_async_call(["second"])
match async_mock.get_last_call():
    Some(call): expect call.args[0] == "second"
    nil: fail "Expected last call"
```

</details>

#### AsyncMock - Error Handling

#### sets error mode

- sets error mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets error mode")
val async_mock = AsyncMock.new("failing")
async_mock.set_error("Network timeout")
expect async_mock.error_mode
expect async_mock.error_message == "Network timeout"
```

</details>

#### records error calls

- records error calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records error calls")
val async_mock = AsyncMock.new("failing_api")
async_mock.set_error("Connection refused")
async_mock.record_async_call(["request"])
val errors = async_mock.get_calls_with_errors()
expect errors.len() == 1
```

</details>

#### clears error mode

- clears error mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears error mode")
val async_mock = AsyncMock.new("recoverable")
async_mock.set_error("Temporary error")
async_mock.clear_error()
expect not async_mock.error_mode
```

</details>

#### AsyncMock - Timing

#### tracks total delay

- tracks total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks total delay")
val async_mock = AsyncMock.new("slow_op")
async_mock.set_delay(50)
async_mock.set_return_values(["r1", "r2", "r3"])
async_mock.record_async_call([])
async_mock.record_async_call([])
async_mock.record_async_call([])
expect async_mock.get_total_delay() == 150
```

</details>

#### resets async mock

- resets async mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets async mock")
val async_mock = AsyncMock.new("resettable")
async_mock.set_return_values(["data"])
async_mock.set_delay(100)
async_mock.record_async_call([])
async_mock.reset()
expect async_mock.call_count() == 0
```

</details>

#### generates summary

- generates summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates summary")
val async_mock = AsyncMock.new("summary_test")
async_mock.set_return_values(["value"])
async_mock.set_delay(25)
async_mock.record_async_call(["input"])
val summary = async_mock.summary()
expect summary.contains("summary_test")
expect summary.contains("1 call")
```

</details>

#### PromiseSequence - Basic

#### creates empty promise sequence

- creates empty promise sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty promise sequence")
val seq = PromiseSequence.new()
expect seq.remaining() == 0
```

</details>

#### adds promise with delay

- adds promise with delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds promise with delay")
val seq = PromiseSequence.new()
seq.add_promise("result", 50)
expect seq.remaining() == 1
```

</details>

#### adds error promise

- adds error promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds error promise")
val seq = PromiseSequence.new()
seq.add_promise_error("timeout", 100)
match seq.peek_next():
    Some(p): expect p.is_error
    nil: fail "Expected promise"
```

</details>

#### PromiseSequence - Iteration

#### gets next promise

- gets next promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets next promise")
val seq = PromiseSequence.new()
seq.add_promise("first", 10)
seq.add_promise("second", 20)
match seq.next_promise():
    Some(p):
        expect p.value == "first"
        expect p.delay_ms == 10
    nil: fail "Expected promise"
expect seq.remaining() == 1
```

</details>

#### returns nil when exhausted

- returns nil when exhausted


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when exhausted")
val seq = PromiseSequence.new()
seq.add_promise("only", 5)
seq.next_promise()
val result = seq.next_promise()
expect result == nil
```

</details>

#### peeks without consuming

- peeks without consuming


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("peeks without consuming")
val seq = PromiseSequence.new()
seq.add_promise("value", 30)
seq.peek_next()
expect seq.remaining() == 1
```

</details>

#### calculates total delay

- calculates total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates total delay")
val seq = PromiseSequence.new()
seq.add_promise("a", 10)
seq.add_promise("b", 20)
seq.add_promise("c", 30)
expect seq.total_delay() == 60
```

</details>

#### resets sequence

- resets sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets sequence")
val seq = PromiseSequence.new()
seq.add_promise("value", 10)
seq.next_promise()
seq.reset()
expect seq.remaining() == 1
```

</details>

#### AsyncSpy - Basic

#### creates async spy

- creates async spy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates async spy")
val spy = AsyncSpy.new("service_spy")
expect spy.name == "service_spy"
expect spy.total_calls() == 0
```

</details>

#### records async call with duration

- records async call with duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records async call with duration")
val spy = AsyncSpy.new("tracker")
spy.record_async_call("fetch", ["url"], 50)
expect spy.total_calls() == 1
```

</details>

#### checks method called

- checks method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks method called")
val spy = AsyncSpy.new("checker")
spy.record_async_call("process", ["data"], 100)
expect spy.method_called("process")
expect not spy.method_called("other")
```

</details>

#### AsyncSpy - Queries

#### gets async calls for method

- gets async calls for method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets async calls for method")
val spy = AsyncSpy.new("multi_spy")
spy.record_async_call("fetch", ["a"], 10)
spy.record_async_call("save", ["b"], 20)
spy.record_async_call("fetch", ["c"], 30)
val fetches = spy.get_async_calls("fetch")
expect fetches.len() == 2
```

</details>

#### calculates timing stats

- calculates timing stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates timing stats")
val spy = AsyncSpy.new("stats_spy")
spy.record_async_call("query", [], 10)
spy.record_async_call("query", [], 20)
spy.record_async_call("query", [], 30)
val stats = spy.get_call_timing_stats("query")
expect stats.min_ms == 10
expect stats.max_ms == 30
expect stats.avg_ms == 20
expect stats.total_ms == 60
expect stats.count == 3
```

</details>

#### generates spy summary

- generates spy summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates spy summary")
val spy = AsyncSpy.new("summary_spy")
spy.record_async_call("method1", [], 15)
val summary = spy.summary()
expect summary.contains("summary_spy")
```

</details>

#### AsyncProtocolMock - Basic

#### creates async protocol mock

- creates async protocol mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
expect proto.method_mocks.len() == 0
```

</details>

#### mocks async method with delay

- mocks async method with delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mocks async method with delay")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("fetchUser", ["id"], 50, "user_data")
expect proto.method_mocks.len() == 1
```

</details>

#### records async method call

- records async method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records async method call")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("getConfig", [], 10, "config_json")
val result = proto.record_async_method_call("getConfig", [])
expect result == "config_json"
```

</details>

#### returns empty for unmocked method

- returns empty for unmocked method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unmocked method")
val proto = AsyncProtocolMock.new()
val result = proto.record_async_method_call("unknown", [])
expect result == ""
```

</details>

#### AsyncProtocolMock - Verification

#### verifies async method called

- verifies async method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies async method called")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("save", ["data"], 100, "saved")
proto.record_async_method_call("save", ["data"])
expect proto.verify_async_method_called("save")
expect not proto.verify_async_method_called("delete")
```

</details>

#### gets async method calls

- gets async method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets async method calls")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("query", ["sql"], 25, "results")
proto.record_async_method_call("query", ["sql"])
proto.record_async_method_call("query", ["sql"])
val calls = proto.get_async_method_calls("query")
expect calls.len() == 2
```

</details>

#### gets async method timing

- gets async method timing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets async method timing")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("slow_op", [], 200, "done")
proto.record_async_method_call("slow_op", [])
val timings = proto.get_async_method_timing("slow_op")
expect timings.len() == 1
expect timings[0] == 200
```

</details>

#### calculates total delay

- calculates total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates total delay")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("op1", [], 50, "r1")
proto.mock_async_method("op2", [], 100, "r2")
proto.record_async_method_call("op1", [])
proto.record_async_method_call("op2", [])
expect proto.get_total_delay() == 150
```

</details>

#### resets async protocol mock

- resets async protocol mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets async protocol mock")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("test", [], 10, "value")
proto.reset()
expect proto.method_mocks.len() == 0
```

</details>

#### AsyncMockComposition - Basic

#### creates async mock composition

- creates async mock composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates async mock composition")
val comp = AsyncMockComposition.new()
expect comp.get_total_calls() == 0
```

</details>

#### adds async mocks

- adds async mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds async mocks")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("api")
val mock2 = AsyncMock.new("db")
comp.add_async_mock("api", mock1)
comp.add_async_mock("db", mock2)
expect comp.get_concurrent_call_count() == 2
```

</details>

#### gets mock by name

- gets mock by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets mock by name")
val comp = AsyncMockComposition.new()
val api_mock = AsyncMock.new("api_service")
comp.add_async_mock("api", api_mock)
match comp.get_mock("api"):
    Some(m): expect m.name == "api_service"
    nil: fail "Expected mock"
```

</details>

#### AsyncMockComposition - Verification

#### verifies all mocks called

- verifies all mocks called


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies all mocks called")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("m1")
val mock2 = AsyncMock.new("m2")
mock1.set_return_values(["r1"])
mock2.set_return_values(["r2"])
comp.add_async_mock("m1", mock1)
comp.add_async_mock("m2", mock2)
expect not comp.verify_all_called()
mock1.record_async_call([])
mock2.record_async_call([])
expect comp.verify_all_called()
```

</details>

#### gets total calls across mocks

- gets total calls across mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets total calls across mocks")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("a")
val mock2 = AsyncMock.new("b")
mock1.set_return_values(["x", "y"])
mock2.set_return_values(["z"])
comp.add_async_mock("a", mock1)
comp.add_async_mock("b", mock2)
mock1.record_async_call([])
mock1.record_async_call([])
mock2.record_async_call([])
expect comp.get_total_calls() == 3
```

</details>

#### gets total delay across mocks

- gets total delay across mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets total delay across mocks")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("slow")
val mock2 = AsyncMock.new("fast")
mock1.set_delay(100)
mock2.set_delay(20)
mock1.set_return_values(["s"])
mock2.set_return_values(["f"])
comp.add_async_mock("slow", mock1)
comp.add_async_mock("fast", mock2)
mock1.record_async_call([])
mock2.record_async_call([])
expect comp.get_total_delay() == 120
```

</details>

#### resets all mocks

- resets all mocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets all mocks")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("r1")
mock1.set_return_values(["v"])
mock1.record_async_call([])
comp.add_async_mock("r1", mock1)
comp.reset_all()
expect comp.get_total_calls() == 0
```

</details>

#### generates composition summary

- generates composition summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates composition summary")
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("service")
comp.add_async_mock("service", mock1)
val summary = comp.summary()
expect summary.contains("AsyncMockComposition")
```

</details>

#### AsyncTimingMatcher - Basic

#### creates within_ms matcher

- creates within_ms matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates within_ms matcher")
val matcher = AsyncTimingMatcher.within_ms(100)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(101)
```

</details>

#### creates at_least_ms matcher

- creates at_least_ms matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates at_least_ms matcher")
val matcher = AsyncTimingMatcher.at_least_ms(50)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(49)
```

</details>

#### creates between_ms matcher

- creates between_ms matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates between_ms matcher")
val matcher = AsyncTimingMatcher.between_ms(10, 100)
expect matcher.matches(10)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(9)
expect not matcher.matches(101)
```

</details>

#### creates exactly_ms matcher

- creates exactly_ms matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates exactly_ms matcher")
val matcher = AsyncTimingMatcher.exactly_ms(42)
expect matcher.matches(42)
expect not matcher.matches(41)
expect not matcher.matches(43)
```

</details>

#### provides description

- provides description


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides description")
val matcher = AsyncTimingMatcher.within_ms(200)
val desc = matcher.get_description()
expect desc.contains("200")
```

</details>

#### Timing Verification Functions

#### verifies async mock timing

- verifies async mock timing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies async mock timing")
val async_mock = AsyncMock.new("timed")
async_mock.set_delay(30)
async_mock.set_return_values(["r1", "r2"])
async_mock.record_async_call([])
async_mock.record_async_call([])
val matcher = AsyncTimingMatcher.within_ms(100)
val total_delay = async_mock.get_total_delay()
expect matcher.matches(total_delay)
```

</details>

#### verifies call timing

- verifies call timing


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies call timing")
val call = AsyncCallRecord(
    args: [],
    timestamp: 0,
    call_number: 0,
    completion_time: 75,
    result: Some("ok"),
    error: nil,
    delay_ms: 75
)
val matcher = AsyncTimingMatcher.between_ms(50, 100)
expect matcher.matches(call.delay_ms)
```

</details>

#### Complex Async Scenarios

#### simulates async API workflow

- simulates async API workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simulates async API workflow")
val proto = AsyncProtocolMock.new()
proto.mock_async_method("authenticate", ["user", "pass"], 50, "token")
proto.mock_async_method("fetchData", ["token"], 100, "data")
proto.mock_async_method("process", ["data"], 25, "result")
val token = proto.record_async_method_call("authenticate", ["user", "pass"])
val data = proto.record_async_method_call("fetchData", [token])
val result = proto.record_async_method_call("process", [data])
expect token == "token"
expect data == "data"
expect result == "result"
expect proto.get_total_delay() == 175
```

</details>

#### handles mixed success and error promises

- handles mixed success and error promises


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed success and error promises")
val seq = PromiseSequence.new()
seq.add_promise("success1", 10)
seq.add_promise_error("timeout", 100)
seq.add_promise("success2", 10)
var success_count = 0
var error_count = 0
while seq.remaining() > 0:
    match seq.next_promise():
        Some(p):
            if p.is_error:
                error_count = error_count + 1
            else:
                success_count = success_count + 1
        nil: true
expect success_count == 2
expect error_count == 1
```

</details>

#### orchestrates multiple async services

- orchestrates multiple async services


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orchestrates multiple async services")
val comp = AsyncMockComposition.new()
val auth = AsyncMock.new("auth")
val db = AsyncMock.new("database")
val cache = AsyncMock.new("cache")
auth.set_delay(50)
db.set_delay(100)
cache.set_delay(10)
auth.set_return_values(["token"])
db.set_return_values(["user_data"])
cache.set_return_values(["cached"])
comp.add_async_mock("auth", auth)
comp.add_async_mock("db", db)
comp.add_async_mock("cache", cache)
auth.record_async_call(["credentials"])
db.record_async_call(["query"])
cache.record_async_call(["key"])
expect comp.verify_all_called()
expect comp.get_total_delay() == 160
val timing_matcher = AsyncTimingMatcher.within_ms(200)
expect timing_matcher.matches(comp.get_total_delay())
```

</details>

#### tracks async spy statistics

- tracks async spy statistics


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks async spy statistics")
val spy = AsyncSpy.new("performance_spy")
spy.record_async_call("api_call", ["1"], 45)
spy.record_async_call("api_call", ["2"], 55)
spy.record_async_call("api_call", ["3"], 50)
spy.record_async_call("db_call", ["q"], 120)
val api_stats = spy.get_call_timing_stats("api_call")
val db_stats = spy.get_call_timing_stats("db_call")
expect api_stats.count == 3
expect api_stats.min_ms == 45
expect api_stats.max_ms == 55
expect db_stats.count == 1
expect db_stats.total_ms == 120
```

</details>

#### Integer Literal Type Inference Fix

#### handles i64 literal in AsyncMock.get_call

- handles i64 literal in AsyncMock.get_call


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles i64 literal in AsyncMock.get_call")
val async_mock = AsyncMock.new("literal_test")
async_mock.set_return_values(["first", "second"])
async_mock.record_async_call(["arg1"])
async_mock.record_async_call(["arg2"])
# This should work with i64 literal 0
val call = async_mock.get_call(0)
expect call.is_some()
match call:
    Some(c): expect c.args[0] == "arg1"
    nil: fail "Should have call"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_phase6_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library - Phase 6 (Async/Await Mocking).
- Mock Library - Phase 6 (Async/Await Mocking)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
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

- Canonical SPipe generation for source `d036318d9a288a74216e70d8870c39b42373f6ed30c977985462dee7ae7bcb0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d036318d9a288a74216e70d8870c39b42373f6ed30c977985462dee7ae7bcb0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d036318d9a288a74216e70d8870c39b42373f6ed30c977985462dee7ae7bcb0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/mock_phase6_spec.spl
mirror: doc/06_spec/01_unit/std/mock_phase6_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_phase6_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_phase6_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/mock_phase6_spec.spl:493:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores async call with timing info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_phase6_spec.spl:509:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores error information' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_phase6_spec.spl:525:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates async mock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
