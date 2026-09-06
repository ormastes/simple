# Mock Specification

> Tests covering Mock Library, MockPolicy, Mock, creation, when/returns stubbing, sequential returns, call recording, verification, reset, Spy, Stub, Argument Matchers, any(), exact(), gt(), lt(), gte(), lte(), in_range(), CallRecorder, CallVerifier, VerifyCount.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Specification

## Scenarios

### Mock Library

### MockPolicy

#### when mode is All

#### allows mock creation

- allows mock creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows mock creation")
mock_policy_init(MockMode.All)
val m = Mock.new("TestMock")
expect m.name == "TestMock"
```

</details>

#### tracks initialization state

- tracks initialization state


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks initialization state")
mock_policy_reset()
expect mock_policy_is_enabled() == true
mock_policy_disable()
expect mock_policy_is_enabled() == false
mock_policy_reset()
```

</details>

#### matches HAL patterns

- matches HAL patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches HAL patterns")
expect mock_policy_matches_hal_pattern("app.hal.gpio") == true
expect mock_policy_matches_hal_pattern("app.sub_hal.spi") == true
expect mock_policy_matches_hal_pattern("app.service.user") == false
```

</details>

#### matches custom patterns

- matches custom patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches custom patterns")
mock_policy_init_with_patterns(["*.cache.*", "*.db.*"])
expect mock_policy_matches_any_pattern("app.cache.redis") == true
expect mock_policy_matches_any_pattern("app.db.postgres") == true
expect mock_policy_matches_any_pattern("app.service.user") == false
mock_policy_reset()
```

</details>

### Mock

### creation

#### creates a mock with a name

- creates a mock with a name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a mock with a name")
val m = Mock.new("UserRepository")
expect m.name == "UserRepository"
```

</details>

#### can use convenience function

- can use convenience function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can use convenience function")
val m = Mock.new("UserRepository")
expect m.name == "UserRepository"
```

</details>

### when/returns stubbing

#### returns configured value

- returns configured value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns configured value")
val m = Mock.new("UserRepo")
m.when("find_by_id").returns(42)
val result = m.call("find_by_id", [])
expect result == 42
```

</details>

#### returns different values for different methods

- returns different values for different methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns different values for different methods")
val m = Mock.new("Service")
m.when("get_name").returns(100)
m.when("get_age").returns(30)
expect m.call("get_name", []) == 100
expect m.call("get_age", []) == 30
```

</details>

#### matches arguments

- matches arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches arguments")
# Real Mock.returns() keys the stub by "method:arg1:arg2:..."
# when with_args() was used, so each arg-specific stub is kept
# independently (unlike the old local reimplementation, which
# silently overwrote the first stub and only ever returned the
# LAST-registered value for every call — a bug in the fake, not
# the real framework).
val m = Mock.new("UserRepo")
m.when("find_by_id").with_args([123]).returns(123)
m.when("find_by_id").with_args([456]).returns(456)
expect m.call("find_by_id", [123]) == 123
expect m.call("find_by_id", [456]) == 456
```

</details>

### sequential returns

#### returns values in sequence

- returns values in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns values in sequence")
val m = Mock.new("Counter")
m.when("next").returns_sequence([1, 2, 3])
expect m.call("next", []) == 1
expect m.call("next", []) == 2
expect m.call("next", []) == 3
expect m.call("next", []) == 1
```

</details>

### call recording

#### records method calls

- records method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records method calls")
val m = Mock.new("Service")
m.when("process").returns(1)
m.call("process", [1, 2, 3])
m.call("process", [4, 5, 6])
expect m.recorder.call_count("process") == 2
```

</details>

#### records calls even without stubs

- records calls even without stubs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records calls even without stubs")
val m = Mock.new("Service")
m.call("unknown", [1])
expect m.recorder.was_called("unknown") == true
```

</details>

### verification

#### verifies method was called

- verifies method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies method was called")
val m = Mock.new("Notifier")
m.when("notify").returns(1)
m.call("notify", [1])
m.verify("notify").was_called().verify()
expect m.recorder.was_called("notify") == true
```

</details>

#### verifies exact call count

- verifies exact call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies exact call count")
val m = Mock.new("Counter")
m.when("increment").returns(1)
m.call("increment", [])
m.call("increment", [])
m.call("increment", [])
m.verify("increment").called_times(3).verify()
expect m.recorder.call_count("increment") == 3
```

</details>

#### verifies method was called once

- verifies method was called once


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies method was called once")
val m = Mock.new("Service")
m.when("init").returns(1)
m.call("init", [])
m.verify("init").once().verify()
expect m.recorder.call_count("init") == 1
```

</details>

#### verifies method was never called

- verifies method was never called


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies method was never called")
val m = Mock.new("Service")
m.verify("shutdown").never().verify()
expect m.recorder.call_count("shutdown") == 0
```

</details>

### reset

#### clears all stubs and calls

- clears all stubs and calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears all stubs and calls")
val m = Mock.new("Service")
m.when("get").returns(42)
m.call("get", [])
m.reset()
expect m.recorder.call_count("get") == 0
```

</details>

### Spy

#### creates a spy with a name

- creates a spy with a name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a spy with a name")
val s = Spy.new("NotificationService")
expect s.name == "NotificationService"
```

</details>

#### records method calls

- records method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records method calls")
val s = Spy.new("Service")
s.record_call("process", [1, 2, 3])
s.record_call("process", [4, 5, 6])
expect s.call_count("process") == 2
```

</details>

#### verifies calls

- verifies calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies calls")
val s = Spy.new("Service")
s.record_call("notify", [1, 123])
s.verify("notify").was_called().verify()
expect s.was_called("notify") == true
```

</details>

#### gets all calls to a method

- gets all calls to a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets all calls to a method")
val s = Spy.new("Service")
s.record_call("log", [1])
s.record_call("log", [2])
val calls = s.calls_to("log")
expect calls.len() == 2
```

</details>

#### resets recorded calls

- resets recorded calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resets recorded calls")
val s = Spy.new("Service")
s.record_call("method", [])
s.reset()
expect s.was_called("method") == false
```

</details>

### Stub

#### creates a stub with a name

- creates a stub with a name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a stub with a name")
val s = Stub.new("Config")
expect s.name == "Config"
```

</details>

#### stores and retrieves values

- stores and retrieves values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores and retrieves values")
val s = Stub.new("Config")
s.set("timeout", 30)
s.set("retries", 3)
expect s.get("timeout") == 30
expect s.get("retries") == 3
```

</details>

#### checks if key exists

- checks if key exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks if key exists")
val s = Stub.new("Config")
s.set("exists", 1)
expect s.has("exists") == true
expect s.has("missing") == false
```

</details>

#### allows chained set calls

- allows chained set calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows chained set calls")
val s = Stub.new("Config").set("a", 1).set("b", 2).set("c", 3)
expect s.get("a") == 1
expect s.get("b") == 2
expect s.get("c") == 3
```

</details>

#### resets all values

- resets all values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resets all values")
val s = Stub.new("Config")
s.set("key", 1)
s.reset()
expect s.has("key") == false
```

</details>

### Argument Matchers

### any()

#### matches any value

- matches any value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches any value")
expect matches_arg(arg_any(), 42) == true
expect matches_arg(arg_any(), 100) == true
```

</details>

### exact()

#### matches exact value

- matches exact value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches exact value")
expect matches_arg(arg_exact(42), 42) == true
expect matches_arg(arg_exact(42), 43) == false
```

</details>

### gt()

#### matches values greater than n

- matches values greater than n


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches values greater than n")
expect matches_arg(arg_gt(10), 15) == true
expect matches_arg(arg_gt(10), 10) == false
expect matches_arg(arg_gt(10), 5) == false
```

</details>

### lt()

#### matches values less than n

- matches values less than n


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches values less than n")
expect matches_arg(arg_lt(10), 5) == true
expect matches_arg(arg_lt(10), 10) == false
expect matches_arg(arg_lt(10), 15) == false
```

</details>

### gte()

#### matches values greater than or equal to n

- matches values greater than or equal to n


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches values greater than or equal to n")
expect matches_arg(arg_gte(10), 15) == true
expect matches_arg(arg_gte(10), 10) == true
expect matches_arg(arg_gte(10), 5) == false
```

</details>

### lte()

#### matches values less than or equal to n

- matches values less than or equal to n


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches values less than or equal to n")
expect matches_arg(arg_lte(10), 5) == true
expect matches_arg(arg_lte(10), 10) == true
expect matches_arg(arg_lte(10), 15) == false
```

</details>

### in_range()

#### matches values within range

- matches values within range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches values within range")
expect matches_arg(arg_in_range(1, 10), 5) == true
expect matches_arg(arg_in_range(1, 10), 1) == true
expect matches_arg(arg_in_range(1, 10), 10) == true
expect matches_arg(arg_in_range(1, 10), 11) == false
```

</details>

### CallRecorder

#### records and retrieves calls

- records and retrieves calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records and retrieves calls")
var recorder = CallRecorder.new()
recorder = recorder.record("method1", [1, 2])
recorder = recorder.record("method2", [3, 4])
recorder = recorder.record("method1", [5, 6])
expect recorder.call_count("method1") == 2
expect recorder.call_count("method2") == 1
expect recorder.call_count("method3") == 0
```

</details>

#### checks if method was called

- checks if method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks if method was called")
var recorder = CallRecorder.new()
recorder = recorder.record("called_method", [])
expect recorder.was_called("called_method") == true
expect recorder.was_called("not_called") == false
```

</details>

#### gets calls for specific method

- gets calls for specific method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets calls for specific method")
var recorder = CallRecorder.new()
recorder = recorder.record("log", [1])
recorder = recorder.record("log", [2])
val log_calls = recorder.calls_for("log")
expect log_calls.len() == 2
```

</details>

#### clears all calls

- clears all calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears all calls")
var recorder = CallRecorder.new()
recorder = recorder.record("method", [])
recorder = recorder.clear()
expect recorder.was_called("method") == false
```

</details>

### CallVerifier

#### verifies at_least calls

- verifies at_least calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies at_least calls")
var recorder = CallRecorder.new()
recorder = recorder.record("method", [])
recorder = recorder.record("method", [])
val verifier = CallVerifier.new(recorder, "method")
verifier.at_least(1).verify()
expect verifier.get_matching_calls().len() >= 1
```

</details>

#### verifies at_most calls

- verifies at_most calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies at_most calls")
var recorder = CallRecorder.new()
recorder = recorder.record("method", [])
val verifier = CallVerifier.new(recorder, "method")
verifier.at_most(1).verify()
expect verifier.get_matching_calls().len() <= 1
```

</details>

### VerifyCount

#### describes count expectations

- describes count expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("describes count expectations")
val recorder = CallRecorder.new()
val verifier = CallVerifier.new(recorder, "method")
expect verifier.once().count_description() == "once"
expect verifier.never().count_description() == "never"
expect verifier.called_times(3).count_description() == "exactly 3 times"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library, MockPolicy, Mock, creation, when/returns stubbing, sequential returns, call recording, verification, reset, Spy, Stub, Argument Matchers, any(), exact(), gt(), lt(), gte(), lte(), in_range(), CallRecorder, CallVerifier, VerifyCount.
- Mock Library
- MockPolicy
- Mock
- creation
- when/returns stubbing
- sequential returns
- call recording
- verification
- reset
- Spy
- Stub
- Argument Matchers
- any()
- exact()
- gt()
- lt()
- gte()
- lte()
- in_range()
- CallRecorder
- CallVerifier
- VerifyCount

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb47c9078279d97a0d48ba6622c63666c0c69a96c266717b3d60a0a4c6e1f419`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb47c9078279d97a0d48ba6622c63666c0c69a96c266717b3d60a0a4c6e1f419`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb47c9078279d97a0d48ba6622c63666c0c69a96c266717b3d60a0a4c6e1f419`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/common/mock_spec.spl
mirror: doc/06_spec/01_unit/lib/common/mock_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/mock_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows mock creation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks initialization state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches HAL patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can use convenience function' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
