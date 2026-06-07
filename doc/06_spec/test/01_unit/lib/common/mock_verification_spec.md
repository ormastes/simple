# Mock Verification Specification

> 1. mock fn expect call

<!-- sdn-diagram:id=mock_verification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_verification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_verification_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_verification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Verification Specification

## Scenarios

### Mock Library - Phase 2 (Verification)

#### Expectations

#### sets expectation for call count

1. mock fn expect call
2. mock fn record call
3. mock fn record call
4. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("handler")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails verification when call count mismatches

1. mock fn expect call
2. mock fn record call
3. mock fn record call
4. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("process")
mock_fn.expect_call(3)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### sets expectation for call arguments

1. mock fn expect call with
2. mock fn record call
3. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("save")
mock_fn.expect_call_with(["id_123", "data"])
mock_fn.record_call(["id_123", "data"])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails when arguments don't match

1. mock fn expect call with
2. mock fn record call
3. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("update")
mock_fn.expect_call_with(["old_value"])
mock_fn.record_call(["new_value"])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### VerificationResult

#### returns success result

1. expect result is ok
2. expect not result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = VerificationResult.success()
expect result.is_ok()
expect not result.is_err()
```

</details>

#### returns failure result with message

1. expect result is err
2. expect not result is ok
3. expect result unwrap err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = VerificationResult.failure("Test failed")
expect result.is_err()
expect not result.is_ok()
expect result.unwrap_err() == "Test failed"
```

</details>

#### Argument Matchers - Equality

#### uses eq matcher for exact match

1. expect matcher matches
2. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.eq("hello")
expect matcher.matches("hello")
expect not matcher.matches("world")
```

</details>

#### uses any matcher for wildcard

1. expect matcher matches
2. expect matcher matches
3. expect matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.any()
expect matcher.matches("anything")
expect matcher.matches("123")
expect matcher.matches("")
```

</details>

#### Argument Matchers - Numeric

#### uses gt matcher for greater than

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches
4. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.gt(10)
expect matcher.matches("15")
expect matcher.matches("100")
expect not matcher.matches("5")
expect not matcher.matches("10")
```

</details>

#### uses lt matcher for less than

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches
4. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.lt(10)
expect matcher.matches("5")
expect matcher.matches("0")
expect not matcher.matches("10")
expect not matcher.matches("15")
```

</details>

#### uses gte matcher for greater or equal

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.gte(10)
expect matcher.matches("10")
expect matcher.matches("15")
expect not matcher.matches("9")
```

</details>

#### uses lte matcher for less or equal

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.lte(10)
expect matcher.matches("10")
expect matcher.matches("5")
expect not matcher.matches("11")
```

</details>

#### Argument Matchers - String Operations

#### uses contains matcher

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.contains("error")
expect matcher.matches("fatal error occurred")
expect matcher.matches("error")
expect not matcher.matches("warning")
```

</details>

#### uses starts_with matcher

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.starts_with("HTTP")
expect matcher.matches("HTTP/1.1")
expect matcher.matches("HTTPS")
expect not matcher.matches("GET HTTP")
```

</details>

#### uses ends_with matcher

1. expect matcher matches
2. expect matcher matches
3. expect not matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matcher = Matcher.ends_with(".json")
expect matcher.matches("config.json")
expect matcher.matches("data.json")
expect not matcher.matches("config.yaml")
```

</details>

#### Call Verification

#### verifies no calls were made

1. expect not mock fn was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("unused")
expect not mock_fn.was_called()
```

</details>

#### verifies single call

1. mock fn record call
2. expect mock fn was called
3. expect mock fn was called n times


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("called_once")
mock_fn.record_call([])
expect mock_fn.was_called()
expect mock_fn.was_called_n_times(1)
```

</details>

#### verifies specific call count

1. mock fn record call
2. mock fn record call
3. mock fn record call
4. expect mock fn was called n times


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("counter")
mock_fn.record_call([])
mock_fn.record_call([])
mock_fn.record_call([])
expect mock_fn.was_called_n_times(3)
```

</details>

#### gets call by index

1. mock fn record call
2. mock fn record call
3. expect first is some
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("api")
mock_fn.record_call(["GET", "/users"])
mock_fn.record_call(["POST", "/users"])
val first = mock_fn.get_call(0)
expect first.is_some()
match first:
    Some(call): expect call.args[0] == "GET"
    nil: fail "Should have call"
```

</details>

#### gets last call

1. mock fn record call
2. mock fn record call
3. mock fn record call
4. expect last is some
5. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("sequence")
mock_fn.record_call(["first"])
mock_fn.record_call(["second"])
mock_fn.record_call(["third"])
val last = mock_fn.get_last_call()
expect last.is_some()
match last:
    Some(call): expect call.args[0] == "third"
    nil: fail "Should have last call"
```

</details>

#### Verification Error Messages

#### provides error message for call count mismatch

1. mock fn expect call
2. mock fn record call
3. expect result is err
4. expect msg contains
5. expect msg contains
6. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("test_fn")
mock_fn.expect_call(2)
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_err()
val msg = result.unwrap_err()
expect msg.contains("test_fn")
expect msg.contains("2")
expect msg.contains("1")
```

</details>

#### provides error message for argument mismatch

1. mock fn expect call with
2. mock fn record call
3. expect result is err
4. expect msg contains
5. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("service")
mock_fn.expect_call_with(["expected_arg"])
mock_fn.record_call(["actual_arg"])
val result = mock_fn.verify()
expect result.is_err()
val msg = result.unwrap_err()
expect msg.contains("service")
expect msg.contains("expected_arg")
```

</details>

#### Multiple Expectations

#### verifies multiple expectations

1. mock fn expect call
2. mock fn record call
3. mock fn record call
4. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("multi")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### resets expectations on reset

1. mock fn expect call
2. mock fn reset
3. mock fn record call
4. mock fn record call
5. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("resettable")
mock_fn.expect_call(1)
mock_fn.reset()
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### Integer Literal Type Inference

#### handles i64 literal in get_call

1. mock fn record call
2. mock fn record call
3. expect call is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("literal_test")
mock_fn.record_call(["first"])
mock_fn.record_call(["second"])
# This should work with i64 literal 0
val call = mock_fn.get_call(0)
expect call.is_some()
```

</details>

#### handles i64 literal in array indexing

1. mock fn record call
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock_fn = MockFunction.new("index_test")
mock_fn.record_call(["value"])
val call = mock_fn.get_call(0)
match call:
    Some(c):
        # Array indexing with i64 literal
        expect c.args[0] == "value"
    nil: fail "Should have call"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mock_verification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mock Library - Phase 2 (Verification)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
