# Mock Phase6 Specification

> 1. result: Some

<!-- sdn-diagram:id=mock_phase6_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_phase6_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_phase6_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_phase6_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. result: Some
2. expect record result is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. error: Some
2. expect record error is some
3. expect record result is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect async mock call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("api_call")
expect async_mock.name == "api_call"
expect async_mock.call_count() == 0
```

</details>

#### sets delay for async mock

1. async mock set delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("fetch")
async_mock.set_delay(100)
expect async_mock.default_delay_ms == 100
```

</details>

#### sets return values

1. async mock set return values
2. expect async mock return values len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("query")
async_mock.set_return_values(["result1", "result2"])
expect async_mock.return_values.len() == 2
```

</details>

#### records async call

1. async mock set return values
2. expect async mock call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("service")
async_mock.set_return_values(["response"])
val result = async_mock.record_async_call(["request"])
expect result == "response"
expect async_mock.call_count() == 1
```

</details>

#### AsyncMock - Verification

#### verifies was called

1. expect not async mock was called
2. async mock set return values
3. async mock record async call
4. expect async mock was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("handler")
expect not async_mock.was_called()
async_mock.set_return_values(["ok"])
async_mock.record_async_call([])
expect async_mock.was_called()
```

</details>

#### verifies was called with args

1. async mock set return values
2. async mock record async call
3. expect async mock was called with
4. expect not async mock was called with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("process")
async_mock.set_return_values(["done"])
async_mock.record_async_call(["arg1", "arg2"])
expect async_mock.was_called_with(["arg1", "arg2"])
expect not async_mock.was_called_with(["other"])
```

</details>

#### gets specific call

1. async mock set return values
2. async mock record async call
3. async mock record async call
4. async mock record async call
5. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. async mock set return values
2. async mock record async call
3. async mock record async call
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. async mock set error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("failing")
async_mock.set_error("Network timeout")
expect async_mock.error_mode
expect async_mock.error_message == "Network timeout"
```

</details>

#### records error calls

1. async mock set error
2. async mock record async call
3. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("failing_api")
async_mock.set_error("Connection refused")
async_mock.record_async_call(["request"])
val errors = async_mock.get_calls_with_errors()
expect errors.len() == 1
```

</details>

#### clears error mode

1. async mock set error
2. async mock clear error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("recoverable")
async_mock.set_error("Temporary error")
async_mock.clear_error()
expect not async_mock.error_mode
```

</details>

#### AsyncMock - Timing

#### tracks total delay

1. async mock set delay
2. async mock set return values
3. async mock record async call
4. async mock record async call
5. async mock record async call
6. expect async mock get total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. async mock set return values
2. async mock set delay
3. async mock record async call
4. async mock reset
5. expect async mock call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_mock = AsyncMock.new("resettable")
async_mock.set_return_values(["data"])
async_mock.set_delay(100)
async_mock.record_async_call([])
async_mock.reset()
expect async_mock.call_count() == 0
```

</details>

#### generates summary

1. async mock set return values
2. async mock set delay
3. async mock record async call
4. expect summary contains
5. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect seq remaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
expect seq.remaining() == 0
```

</details>

#### adds promise with delay

1. seq add promise
2. expect seq remaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise("result", 50)
expect seq.remaining() == 1
```

</details>

#### adds error promise

1. seq add promise error
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise_error("timeout", 100)
match seq.peek_next():
    Some(p): expect p.is_error
    nil: fail "Expected promise"
```

</details>

#### PromiseSequence - Iteration

#### gets next promise

1. seq add promise
2. seq add promise
3. Some
4. expect seq remaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. seq add promise
2. seq next promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise("only", 5)
seq.next_promise()
val result = seq.next_promise()
expect result == nil
```

</details>

#### peeks without consuming

1. seq add promise
2. seq peek next
3. expect seq remaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise("value", 30)
seq.peek_next()
expect seq.remaining() == 1
```

</details>

#### calculates total delay

1. seq add promise
2. seq add promise
3. seq add promise
4. expect seq total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise("a", 10)
seq.add_promise("b", 20)
seq.add_promise("c", 30)
expect seq.total_delay() == 60
```

</details>

#### resets sequence

1. seq add promise
2. seq next promise
3. seq reset
4. expect seq remaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = PromiseSequence.new()
seq.add_promise("value", 10)
seq.next_promise()
seq.reset()
expect seq.remaining() == 1
```

</details>

#### AsyncSpy - Basic

#### creates async spy

1. expect spy total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spy = AsyncSpy.new("service_spy")
expect spy.name == "service_spy"
expect spy.total_calls() == 0
```

</details>

#### records async call with duration

1. spy record async call
2. expect spy total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spy = AsyncSpy.new("tracker")
spy.record_async_call("fetch", ["url"], 50)
expect spy.total_calls() == 1
```

</details>

#### checks method called

1. spy record async call
2. expect spy method called
3. expect not spy method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spy = AsyncSpy.new("checker")
spy.record_async_call("process", ["data"], 100)
expect spy.method_called("process")
expect not spy.method_called("other")
```

</details>

#### AsyncSpy - Queries

#### gets async calls for method

1. spy record async call
2. spy record async call
3. spy record async call
4. expect fetches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spy = AsyncSpy.new("multi_spy")
spy.record_async_call("fetch", ["a"], 10)
spy.record_async_call("save", ["b"], 20)
spy.record_async_call("fetch", ["c"], 30)
val fetches = spy.get_async_calls("fetch")
expect fetches.len() == 2
```

</details>

#### calculates timing stats

1. spy record async call
2. spy record async call
3. spy record async call


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. spy record async call
2. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spy = AsyncSpy.new("summary_spy")
spy.record_async_call("method1", [], 15)
val summary = spy.summary()
expect summary.contains("summary_spy")
```

</details>

#### AsyncProtocolMock - Basic

#### creates async protocol mock

1. expect proto method mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
expect proto.method_mocks.len() == 0
```

</details>

#### mocks async method with delay

1. proto mock async method
2. expect proto method mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("fetchUser", ["id"], 50, "user_data")
expect proto.method_mocks.len() == 1
```

</details>

#### records async method call

1. proto mock async method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("getConfig", [], 10, "config_json")
val result = proto.record_async_method_call("getConfig", [])
expect result == "config_json"
```

</details>

#### returns empty for unmocked method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
val result = proto.record_async_method_call("unknown", [])
expect result == ""
```

</details>

#### AsyncProtocolMock - Verification

#### verifies async method called

1. proto mock async method
2. proto record async method call
3. expect proto verify async method called
4. expect not proto verify async method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("save", ["data"], 100, "saved")
proto.record_async_method_call("save", ["data"])
expect proto.verify_async_method_called("save")
expect not proto.verify_async_method_called("delete")
```

</details>

#### gets async method calls

1. proto mock async method
2. proto record async method call
3. proto record async method call
4. expect calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("query", ["sql"], 25, "results")
proto.record_async_method_call("query", ["sql"])
proto.record_async_method_call("query", ["sql"])
val calls = proto.get_async_method_calls("query")
expect calls.len() == 2
```

</details>

#### gets async method timing

1. proto mock async method
2. proto record async method call
3. expect timings len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("slow_op", [], 200, "done")
proto.record_async_method_call("slow_op", [])
val timings = proto.get_async_method_timing("slow_op")
expect timings.len() == 1
expect timings[0] == 200
```

</details>

#### calculates total delay

1. proto mock async method
2. proto mock async method
3. proto record async method call
4. proto record async method call
5. expect proto get total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("op1", [], 50, "r1")
proto.mock_async_method("op2", [], 100, "r2")
proto.record_async_method_call("op1", [])
proto.record_async_method_call("op2", [])
expect proto.get_total_delay() == 150
```

</details>

#### resets async protocol mock

1. proto mock async method
2. proto reset
3. expect proto method mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = AsyncProtocolMock.new()
proto.mock_async_method("test", [], 10, "value")
proto.reset()
expect proto.method_mocks.len() == 0
```

</details>

#### AsyncMockComposition - Basic

#### creates async mock composition

1. expect comp get total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = AsyncMockComposition.new()
expect comp.get_total_calls() == 0
```

</details>

#### adds async mocks

1. comp add async mock
2. comp add async mock
3. expect comp get concurrent call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("api")
val mock2 = AsyncMock.new("db")
comp.add_async_mock("api", mock1)
comp.add_async_mock("db", mock2)
expect comp.get_concurrent_call_count() == 2
```

</details>

#### gets mock by name

1. comp add async mock
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mock1 set return values
2. mock2 set return values
3. comp add async mock
4. comp add async mock
5. expect not comp verify all called
6. mock1 record async call
7. mock2 record async call
8. expect comp verify all called


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mock1 set return values
2. mock2 set return values
3. comp add async mock
4. comp add async mock
5. mock1 record async call
6. mock1 record async call
7. mock2 record async call
8. expect comp get total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mock1 set delay
2. mock2 set delay
3. mock1 set return values
4. mock2 set return values
5. comp add async mock
6. comp add async mock
7. mock1 record async call
8. mock2 record async call
9. expect comp get total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mock1 set return values
2. mock1 record async call
3. comp add async mock
4. comp reset all
5. expect comp get total calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. comp add async mock
2. expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = AsyncMockComposition.new()
val mock1 = AsyncMock.new("service")
comp.add_async_mock("service", mock1)
val summary = comp.summary()
expect summary.contains("AsyncMockComposition")
```

</details>

#### AsyncTimingMatcher - Basic

#### creates within_ms matcher

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = AsyncTimingMatcher.within_ms(100)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(101)
```

</details>

#### creates at_least_ms matcher

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = AsyncTimingMatcher.at_least_ms(50)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(49)
```

</details>

#### creates between_ms matcher

1. expect matcher matches
2. expect matcher matches
3. expect matcher matches
4. expect not matcher matches
5. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = AsyncTimingMatcher.between_ms(10, 100)
expect matcher.matches(10)
expect matcher.matches(50)
expect matcher.matches(100)
expect not matcher.matches(9)
expect not matcher.matches(101)
```

</details>

#### creates exactly_ms matcher

1. expect matcher matches
2. expect not matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = AsyncTimingMatcher.exactly_ms(42)
expect matcher.matches(42)
expect not matcher.matches(41)
expect not matcher.matches(43)
```

</details>

#### provides description

1. expect desc contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = AsyncTimingMatcher.within_ms(200)
val desc = matcher.get_description()
expect desc.contains("200")
```

</details>

#### Timing Verification Functions

#### verifies async mock timing

1. async mock set delay
2. async mock set return values
3. async mock record async call
4. async mock record async call
5. expect matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. result: Some
2. expect matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. proto mock async method
2. proto mock async method
3. proto mock async method
4. expect proto get total delay


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. seq add promise
2. seq add promise error
3. seq add promise
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. auth set delay
2. db set delay
3. cache set delay
4. auth set return values
5. db set return values
6. cache set return values
7. comp add async mock
8. comp add async mock
9. comp add async mock
10. auth record async call
11. db record async call
12. cache record async call
13. expect comp verify all called
14. expect comp get total delay
15. expect timing matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. spy record async call
2. spy record async call
3. spy record async call
4. spy record async call


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. async mock set return values
2. async mock record async call
3. async mock record async call
4. expect call is some
5. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/mock_phase6_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
