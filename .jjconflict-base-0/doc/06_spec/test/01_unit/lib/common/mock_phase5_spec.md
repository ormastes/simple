# Mock Phase5 Specification

> <details>

<!-- sdn-diagram:id=mock_phase5_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_phase5_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_phase5_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_phase5_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Phase5 Specification

## Scenarios

### Mock Library - Phase 5 (Trait-Based Mocking)

#### Fluent Expectations

#### creates fluent expectation for mock

- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("service")
val fluent = FluentExpectation.create(mockfn)
expect fluent.mockfn.name == "service"
val has_when_args = match fluent.when_args:
    Some(_): true
    nil: false
expect not has_when_args
```

</details>

#### sets when clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("api")
val fluent = FluentExpectation.create(mockfn)
val with_when = fluent.when_called_with(["GET", "/users"])
expect with_when.when_args.?
```

</details>

#### chains when with returns

- var w = fluent when called with
- w returns
- expect rv len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("fetch")
val fluent = FluentExpectation.create(mockfn)
var w = fluent.when_called_with(["data"])
w.returns("result")
var fm = w.mockfn
var rv = fm.return_values
expect rv.len() > 0
```

</details>

#### When Builder

#### creates when builder for mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("handler")
val when = WhenBuilder.create(mockfn)
expect when.mockfn.name == "handler"
```

</details>

#### sets predicate condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("validator")
val when_builder = WhenBuilder.create(mockfn)
val cond = _1.len() > 0 and _1[0] == "valid"
val with_condition = when_builder.when(cond)
expect with_condition.mockfn.name == "validator"
```

</details>

#### chains when with returns

- when builder when


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mockfn = MockFunction.create("processor")
val when_builder = WhenBuilder.create(mockfn)
val cond = _1.len() == 1
when_builder.when(cond).returns("processed")
```

</details>

#### Protocol Mock - Basic

#### creates protocol mock

- expect proto method mocks len
- expect proto recorded calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
expect proto.method_mocks.len() == 0
expect proto.recorded_calls.len() == 0
```

</details>

#### mocks method with return value

- proto mock method
- expect proto method mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="getName", args=[], return_value="John")
expect proto.method_mocks.len() == 1
```

</details>

#### records method call

- proto mock method
- var result = proto record method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="getValue", args=["key"], return_value="value")
var result = proto.record_method_call("getValue", ["key"])
expect result == "value"
```

</details>

#### returns empty string for unmocked method

- var result = proto record method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
var result = proto.record_method_call("unmocked", [])
expect result == ""
```

</details>

#### Protocol Mock - Verification

#### verifies method was called

- proto mock method
- proto record method call
- expect proto verify method called
- expect not proto verify method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="process", args=["data"], return_value="done")
proto.record_method_call("process", ["data"])
expect proto.verify_method_called("process")
expect not proto.verify_method_called("other")
```

</details>

#### gets all calls to a method

- proto mock method
- proto mock method
- proto record method call
- proto record method call
- var calls = proto get method calls
- expect calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="compute", args=["a"], return_value="result_a")
proto.mock_method(name="compute", args=["b"], return_value="result_b")
proto.record_method_call("compute", ["a"])
proto.record_method_call("compute", ["a"])
var calls = proto.get_method_calls("compute")
expect calls.len() == 2
```

</details>

#### resets protocol mock

- proto mock method
- expect proto method mocks len
- proto reset
- expect proto method mocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="test", args=[], return_value="value")
expect proto.method_mocks.len() == 1
proto.reset()
expect proto.method_mocks.len() == 0
```

</details>

#### Protocol Mock - Argument Matching

#### matches exact arguments

- proto mock method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="api", args=["GET", "/users"], return_value="data")
val result1 = proto.record_method_call("api", ["GET", "/users"])
val result2 = proto.record_method_call("api", ["POST", "/users"])
expect result1 == "data"
expect result2 == ""
```

</details>

#### handles multiple method signatures

- proto mock method
- proto mock method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="save", args=["user"], return_value="saved")
proto.mock_method(name="save", args=["user", "timestamp"], return_value="saved_with_time")
val r1 = proto.record_method_call("save", ["user"])
val r2 = proto.record_method_call("save", ["user", "timestamp"])
expect r1 == "saved"
expect r2 == "saved_with_time"
```

</details>

#### Auto Mock - Setup

#### creates auto mock

- expect auto mock properties len
- expect auto mock methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("User")
expect auto_mock.name == "User"
expect auto_mock.properties.len() == 0
expect auto_mock.methods.len() == 0
```

</details>

#### adds properties

- auto mock add property
- auto mock add property
- expect props len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Service")
auto_mock.add_property("config")
auto_mock.add_property("state")
val props = auto_mock.get_properties()
expect props.len() == 2
expect props[0] == "config"
```

</details>

#### sets up methods

- auto mock setup method
- auto mock setup method
- expect auto mock methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Handler")
auto_mock.setup_method(method_name="process", args=["data"], return_value="result")
auto_mock.setup_method(method_name="validate", args=["input"], return_value="valid")
expect auto_mock.methods.len() == 2
```

</details>

#### Auto Mock - Method Calls

#### calls mocked method

- auto mock setup method
- var result = auto mock call method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Calculator")
auto_mock.setup_method(method_name="add", args=["1", "2"], return_value="3")
var result = auto_mock.call_method("add", ["1", "2"])
expect result == "3"
```

</details>

#### returns empty for unmocked method

- var result = auto mock call method


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Service")
var result = auto_mock.call_method("unknown", [])
expect result == ""
```

</details>

#### distinguishes between method signatures

- auto mock setup method
- auto mock setup method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Store")
auto_mock.setup_method(method_name="get", args=["key"], return_value="value")
auto_mock.setup_method(method_name="get", args=["key", "default"], return_value="value_or_default")
val r1 = auto_mock.call_method("get", ["key"])
val r2 = auto_mock.call_method("get", ["key", "default"])
expect r1 == "value"
expect r2 == "value_or_default"
```

</details>

#### Auto Mock - Retrieval

#### gets all properties

- auto mock add property
- auto mock add property
- auto mock add property
- expect props len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Entity")
auto_mock.add_property("id")
auto_mock.add_property("name")
auto_mock.add_property("email")
val props = auto_mock.get_properties()
expect props.len() == 3
```

</details>

#### gets all methods

- auto mock setup method
- auto mock setup method
- auto mock setup method
- expect methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Interface")
auto_mock.setup_method(method_name="method1", args=[], return_value="r1")
auto_mock.setup_method(method_name="method2", args=["arg"], return_value="r2")
auto_mock.setup_method(method_name="method3", args=["a", "b"], return_value="r3")
var methods = auto_mock.methods
expect methods.len() == 3
```

</details>

#### generates auto mock summary

- auto mock add property
- auto mock setup method
- expect summary contains
- expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Service")
auto_mock.add_property("config")
auto_mock.setup_method(method_name="init", args=[], return_value="initialized")
val summary = auto_mock.summary()
expect summary.contains("Service")
expect summary.contains("1")
```

</details>

#### Complex Phase 5 Scenarios

#### combines protocol mock with fluent expectation

- proto mock method
- proto record method call
- expect proto verify method called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="fetch", args=["id"], return_value="record")
proto.record_method_call("fetch", ["id"])
expect proto.verify_method_called("fetch")
```

</details>

#### auto mock with multiple method signatures

- auto mock setup method
- auto mock setup method
- auto mock setup method
- auto mock call method
- auto mock call method
- auto mock call method
- expect calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("API")
auto_mock.setup_method(method_name="request", args=["GET"], return_value="success")
auto_mock.setup_method(method_name="request", args=["POST", "data"], return_value="created")
auto_mock.setup_method(method_name="request", args=["DELETE", "id"], return_value="deleted")
var calls = [
    auto_mock.call_method("request", ["GET"]),
    auto_mock.call_method("request", ["POST", "data"]),
    auto_mock.call_method("request", ["DELETE", "id"])
]
expect calls.len() == 3
expect calls[0] == "success"
```

</details>

#### protocol mock for complex workflow

- proto mock method
- proto mock method
- proto mock method


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = ProtocolMock.create()
proto.mock_method(name="authenticate", args=["user", "pass"], return_value="token_123")
proto.mock_method(name="authorize", args=["token_123"], return_value="allowed")
proto.mock_method(name="execute", args=["cmd"], return_value="success")
val auth = proto.record_method_call("authenticate", ["user", "pass"])
val authz = proto.record_method_call("authorize", [auth])
val exec = proto.record_method_call("execute", ["cmd"])
expect auth == "token_123"
expect authz == "allowed"
expect exec == "success"
```

</details>

#### creates mock interface simulation

- auto mock setup method
- auto mock setup method
- auto mock setup method
- expect auto mock call method
- expect auto mock call method
- expect auto mock call method
- expect summary contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auto_mock = AutoMock.create("Database")
auto_mock.setup_method(method_name="connect", args=["host", "port"], return_value="connected")
auto_mock.setup_method(method_name="query", args=["SELECT *"], return_value="rows")
auto_mock.setup_method(method_name="disconnect", args=[], return_value="closed")
expect auto_mock.call_method("connect", ["host", "port"]) == "connected"
expect auto_mock.call_method("query", ["SELECT *"]) == "rows"
expect auto_mock.call_method("disconnect", []) == "closed"
val summary = auto_mock.summary()
expect summary.contains("Database")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mock_phase5_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mock Library - Phase 5 (Trait-Based Mocking)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
