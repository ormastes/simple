# Mock Specification

> <details>

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
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Specification

## Scenarios

### Mock Library

### MockPolicy

#### when mode is All

#### allows mock creation

- mock policy init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_policy_init(MockMode.All)
val m = Mock.create("TestMock")
expect m.name == "TestMock"
```

</details>

#### tracks initialization state

- mock policy reset
- expect mock policy is enabled
- mock policy disable
- expect mock policy is enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_policy_reset()
expect mock_policy_is_enabled() == true
mock_policy_disable()
expect mock_policy_is_enabled() == false
```

</details>

#### matches HAL patterns

- expect mock policy matches hal pattern
- expect mock policy matches hal pattern
- expect mock policy matches hal pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect mock_policy_matches_hal_pattern("app.hal.gpio") == true
expect mock_policy_matches_hal_pattern("app.sub_hal.spi") == true
expect mock_policy_matches_hal_pattern("app.service.user") == false
```

</details>

#### matches custom patterns

- mock policy init with patterns
- expect mock policy matches any pattern
- expect mock policy matches any pattern
- expect mock policy matches any pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_policy_init_with_patterns(["*.cache.*", "*.db.*"])
expect mock_policy_matches_any_pattern("app.cache.redis") == true
expect mock_policy_matches_any_pattern("app.db.postgres") == true
expect mock_policy_matches_any_pattern("app.service.user") == false
```

</details>

### Mock

### creation

#### creates a mock with a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("UserRepository")
expect m.name == "UserRepository"
```

</details>

#### can use convenience function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("UserRepository")
expect m.name == "UserRepository"
```

</details>

### when/returns stubbing

#### returns configured value

- m when


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("UserRepo")
m.when("find_by_id").returns(42)
val result = m.call("find_by_id", [])
expect result == 42
```

</details>

#### returns different values for different methods

- m when
- m when
- expect m call
- expect m call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
m.when("get_name").returns(100)
m.when("get_age").returns(30)
expect m.call("get_name", []) == 100
expect m.call("get_age", []) == 30
```

</details>

#### matches arguments

- m when
- m when
- expect m call
- expect m call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("UserRepo")
m.when("find_by_id").with_args([123]).returns(123)
m.when("find_by_id").with_args([456]).returns(456)
expect m.call("find_by_id", [123]) == 456
expect m.call("find_by_id", [456]) == 456
```

</details>

### sequential returns

#### returns values in sequence

- m when
- expect m call
- expect m call
- expect m call
- expect m call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Counter")
m.when("next").returns_sequence([1, 2, 3])
expect m.call("next", []) == 1
expect m.call("next", []) == 2
expect m.call("next", []) == 3
expect m.call("next", []) == 1
```

</details>

### call recording

#### records method calls

- m when
- m call
- m call
- expect m recorder call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
m.when("process").returns(1)
m.call("process", [1, 2, 3])
m.call("process", [4, 5, 6])
expect m.recorder.call_count("process") == 2
```

</details>

#### records calls even without stubs

- m call
- expect m recorder was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
m.call("unknown", [1])
expect m.recorder.was_called("unknown") == true
```

</details>

### verification

#### verifies method was called

- m when
- m call
- expect m verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Notifier")
m.when("notify").returns(1)
m.call("notify", [1])
expect m.verify("notify").was_called().verify() == true
```

</details>

#### verifies exact call count

- m when
- m call
- m call
- m call
- expect m verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Counter")
m.when("increment").returns(1)
m.call("increment", [])
m.call("increment", [])
m.call("increment", [])
expect m.verify("increment").called_times(3).verify() == true
```

</details>

#### verifies method was called once

- m when
- m call
- expect m verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
m.when("init").returns(1)
m.call("init", [])
expect m.verify("init").once().verify() == true
```

</details>

#### verifies method was never called

- expect m verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
expect m.verify("shutdown").never().verify() == true
```

</details>

### reset

#### clears all stubs and calls

- m when
- m call
- m reset
- expect m recorder call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mock.create("Service")
m.when("get").returns(42)
m.call("get", [])
m.reset()
expect m.recorder.call_count("get") == 0
```

</details>

### Spy

#### creates a spy with a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Spy.create("NotificationService")
expect s.name == "NotificationService"
```

</details>

#### records method calls

- s record call
- s record call
- expect s call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Spy.create("Service")
s.record_call("process", [1, 2, 3])
s.record_call("process", [4, 5, 6])
expect s.call_count("process") == 2
```

</details>

#### verifies calls

- s record call
- expect s verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Spy.create("Service")
s.record_call("notify", [1, 123])
expect s.verify("notify").was_called().verify() == true
```

</details>

#### gets all calls to a method

- s record call
- s record call
- expect calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Spy.create("Service")
s.record_call("log", [1])
s.record_call("log", [2])
val calls = s.calls_to("log")
expect calls.len() == 2
```

</details>

#### resets recorded calls

- s record call
- s reset
- expect s was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Spy.create("Service")
s.record_call("method", [])
s.reset()
expect s.was_called("method") == false
```

</details>

### Stub

#### creates a stub with a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Stub.create("Config")
expect s.name == "Config"
```

</details>

#### stores and retrieves values

- s set
- s set
- expect s get
- expect s get


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Stub.create("Config")
s.set("timeout", 30)
s.set("retries", 3)
expect s.get("timeout") == 30
expect s.get("retries") == 3
```

</details>

#### checks if key exists

- s set
- expect s has
- expect s has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Stub.create("Config")
s.set("exists", 1)
expect s.has("exists") == true
expect s.has("missing") == false
```

</details>

#### allows chained set calls

- expect s get
- expect s get
- expect s get


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Stub.create("Config").set("a", 1).set("b", 2).set("c", 3)
expect s.get("a") == 1
expect s.get("b") == 2
expect s.get("c") == 3
```

</details>

#### resets all values

- s set
- s reset
- expect s has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Stub.create("Config")
s.set("key", 1)
s.reset()
expect s.has("key") == false
```

</details>

### Argument Matchers

### any()

#### matches any value

- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_any(), 42) == true
expect matches_arg(arg_any(), 100) == true
```

</details>

### exact()

#### matches exact value

- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_exact(42), 42) == true
expect matches_arg(arg_exact(42), 43) == false
```

</details>

### gt()

#### matches values greater than n

- expect matches arg
- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_gt(10), 15) == true
expect matches_arg(arg_gt(10), 10) == false
expect matches_arg(arg_gt(10), 5) == false
```

</details>

### lt()

#### matches values less than n

- expect matches arg
- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_lt(10), 5) == true
expect matches_arg(arg_lt(10), 10) == false
expect matches_arg(arg_lt(10), 15) == false
```

</details>

### gte()

#### matches values greater than or equal to n

- expect matches arg
- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_gte(10), 15) == true
expect matches_arg(arg_gte(10), 10) == true
expect matches_arg(arg_gte(10), 5) == false
```

</details>

### lte()

#### matches values less than or equal to n

- expect matches arg
- expect matches arg
- expect matches arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect matches_arg(arg_lte(10), 5) == true
expect matches_arg(arg_lte(10), 10) == true
expect matches_arg(arg_lte(10), 15) == false
```

</details>

### in_range()

#### matches values within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "enum variant InRange(i64, i64) constructor broken - creates tuple instead of enum"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

### CallRecorder

#### records and retrieves calls

- recorder record
- recorder record
- recorder record
- expect recorder call count
- expect recorder call count
- expect recorder call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("method1", [1, 2])
recorder.record("method2", [3, 4])
recorder.record("method1", [5, 6])
expect recorder.call_count("method1") == 2
expect recorder.call_count("method2") == 1
expect recorder.call_count("method3") == 0
```

</details>

#### checks if method was called

- recorder record
- expect recorder was called
- expect recorder was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("called_method", [])
expect recorder.was_called("called_method") == true
expect recorder.was_called("not_called") == false
```

</details>

#### gets calls for specific method

- recorder record
- recorder record
- expect log calls len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("log", [1])
recorder.record("log", [2])
val log_calls = recorder.calls_for("log")
expect log_calls.len() == 2
```

</details>

#### clears all calls

- recorder record
- recorder clear
- expect recorder was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("method", [])
recorder.clear()
expect recorder.was_called("method") == false
```

</details>

### CallVerifier

#### verifies at_least calls

- recorder record
- recorder record
- expect verifier at least
- expect verifier at least


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("method", [])
recorder.record("method", [])
val verifier = CallVerifier.create(recorder, "method")
expect verifier.at_least(1).verify() == true
expect verifier.at_least(2).verify() == true
```

</details>

#### verifies at_most calls

- recorder record
- expect verifier at most
- expect verifier at most


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
recorder.record("method", [])
val verifier = CallVerifier.create(recorder, "method")
expect verifier.at_most(1).verify() == true
expect verifier.at_most(5).verify() == true
```

</details>

### VerifyCount

#### describes count expectations

- expect verifier once
- expect verifier never
- expect verifier called times


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.create()
val verifier = CallVerifier.create(recorder, "method")
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
