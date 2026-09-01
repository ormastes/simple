# Mock Phase5 Specification

> Tests covering Mock Library - Phase 5 (Trait-Based Mocking).

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

- creates fluent expectation for mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates fluent expectation for mock")
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

- sets when clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets when clause")
val mockfn = MockFunction.create("api")
val fluent = FluentExpectation.create(mockfn)
val with_when = fluent.when_called_with(["GET", "/users"])
expect with_when.when_args.?
```

</details>

#### chains when with returns

- chains when with returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains when with returns")
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

- creates when builder for mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates when builder for mock")
val mockfn = MockFunction.create("handler")
val when = WhenBuilder.create(mockfn)
expect when.mockfn.name == "handler"
```

</details>

#### sets predicate condition

- sets predicate condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets predicate condition")
val mockfn = MockFunction.create("validator")
val when_builder = WhenBuilder.create(mockfn)
val cond = _1.len() > 0 and _1[0] == "valid"
val with_condition = when_builder.when(cond)
expect with_condition.mockfn.name == "validator"
```

</details>

#### chains when with returns

- chains when with returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains when with returns")
val mockfn = MockFunction.create("processor")
val when_builder = WhenBuilder.create(mockfn)
val cond = _1.len() == 1
when_builder.when(cond).returns("processed")
```

</details>

#### Protocol Mock - Basic

#### creates protocol mock

- creates protocol mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates protocol mock")
val proto = ProtocolMock.create()
expect proto.method_mocks.len() == 0
expect proto.recorded_calls.len() == 0
```

</details>

#### mocks method with return value

- mocks method with return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mocks method with return value")
val proto = ProtocolMock.create()
proto.mock_method(name="getName", args=[], return_value="John")
expect proto.method_mocks.len() == 1
```

</details>

#### records method call

- records method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records method call")
val proto = ProtocolMock.create()
proto.mock_method(name="getValue", args=["key"], return_value="value")
var result = proto.record_method_call("getValue", ["key"])
expect result == "value"
```

</details>

#### returns empty string for unmocked method

- returns empty string for unmocked method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for unmocked method")
val proto = ProtocolMock.create()
var result = proto.record_method_call("unmocked", [])
expect result == ""
```

</details>

#### Protocol Mock - Verification

#### verifies method was called

- verifies method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies method was called")
val proto = ProtocolMock.create()
proto.mock_method(name="process", args=["data"], return_value="done")
proto.record_method_call("process", ["data"])
expect proto.verify_method_called("process")
expect not proto.verify_method_called("other")
```

</details>

#### gets all calls to a method

- gets all calls to a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets all calls to a method")
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

- resets protocol mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets protocol mock")
val proto = ProtocolMock.create()
proto.mock_method(name="test", args=[], return_value="value")
expect proto.method_mocks.len() == 1
proto.reset()
expect proto.method_mocks.len() == 0
```

</details>

#### Protocol Mock - Argument Matching

#### matches exact arguments

- matches exact arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact arguments")
val proto = ProtocolMock.create()
proto.mock_method(name="api", args=["GET", "/users"], return_value="data")
val result1 = proto.record_method_call("api", ["GET", "/users"])
val result2 = proto.record_method_call("api", ["POST", "/users"])
expect result1 == "data"
expect result2 == ""
```

</details>

#### handles multiple method signatures

- handles multiple method signatures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple method signatures")
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

- creates auto mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates auto mock")
val auto_mock = AutoMock.create("User")
expect auto_mock.name == "User"
expect auto_mock.properties.len() == 0
expect auto_mock.methods.len() == 0
```

</details>

#### adds properties

- adds properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds properties")
val auto_mock = AutoMock.create("Service")
auto_mock.add_property("config")
auto_mock.add_property("state")
val props = auto_mock.get_properties()
expect props.len() == 2
expect props[0] == "config"
```

</details>

#### sets up methods

- sets up methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets up methods")
val auto_mock = AutoMock.create("Handler")
auto_mock.setup_method(method_name="process", args=["data"], return_value="result")
auto_mock.setup_method(method_name="validate", args=["input"], return_value="valid")
expect auto_mock.methods.len() == 2
```

</details>

#### Auto Mock - Method Calls

#### calls mocked method

- calls mocked method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls mocked method")
val auto_mock = AutoMock.create("Calculator")
auto_mock.setup_method(method_name="add", args=["1", "2"], return_value="3")
var result = auto_mock.call_method("add", ["1", "2"])
expect result == "3"
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
val auto_mock = AutoMock.create("Service")
var result = auto_mock.call_method("unknown", [])
expect result == ""
```

</details>

#### distinguishes between method signatures

- distinguishes between method signatures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes between method signatures")
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

- gets all properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets all properties")
val auto_mock = AutoMock.create("Entity")
auto_mock.add_property("id")
auto_mock.add_property("name")
auto_mock.add_property("email")
val props = auto_mock.get_properties()
expect props.len() == 3
```

</details>

#### gets all methods

- gets all methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets all methods")
val auto_mock = AutoMock.create("Interface")
auto_mock.setup_method(method_name="method1", args=[], return_value="r1")
auto_mock.setup_method(method_name="method2", args=["arg"], return_value="r2")
auto_mock.setup_method(method_name="method3", args=["a", "b"], return_value="r3")
var methods = auto_mock.methods
expect methods.len() == 3
```

</details>

#### generates auto mock summary

- generates auto mock summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates auto mock summary")
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

- combines protocol mock with fluent expectation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines protocol mock with fluent expectation")
val proto = ProtocolMock.create()
proto.mock_method(name="fetch", args=["id"], return_value="record")
proto.record_method_call("fetch", ["id"])
expect proto.verify_method_called("fetch")
```

</details>

#### auto mock with multiple method signatures

- auto mock with multiple method signatures


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto mock with multiple method signatures")
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

- protocol mock for complex workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("protocol mock for complex workflow")
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

- creates mock interface simulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mock interface simulation")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library - Phase 5 (Trait-Based Mocking).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1bb1ec0141d4bf43d663649305f8ce70da4f6f45f090d9677ed2684a9e6b83c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1bb1ec0141d4bf43d663649305f8ce70da4f6f45f090d9677ed2684a9e6b83c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1bb1ec0141d4bf43d663649305f8ce70da4f6f45f090d9677ed2684a9e6b83c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/mock_phase5_spec.spl
mirror: doc/06_spec/01_unit/lib/common/mock_phase5_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/mock_phase5_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/mock_phase5_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/mock_phase5_spec.spl:399:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates fluent expectation for mock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_phase5_spec.spl:410:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets when clause' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_phase5_spec.spl:418:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains when with returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
