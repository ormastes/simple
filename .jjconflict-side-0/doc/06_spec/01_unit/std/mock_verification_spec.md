# Mock Verification Specification

> Tests covering Mock Library - Phase 2 (Verification).

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

- sets expectation for call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets expectation for call count")
val mock_fn = MockFunction.new("handler")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails verification when call count mismatches

- fails verification when call count mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails verification when call count mismatches")
val mock_fn = MockFunction.new("process")
mock_fn.expect_call(3)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### sets expectation for call arguments

- sets expectation for call arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets expectation for call arguments")
val mock_fn = MockFunction.new("save")
mock_fn.expect_call_with(["id_123", "data"])
mock_fn.record_call(["id_123", "data"])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails when arguments don't match

- fails when arguments don't match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when arguments don't match")
val mock_fn = MockFunction.new("update")
mock_fn.expect_call_with(["old_value"])
mock_fn.record_call(["new_value"])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### VerificationResult

#### returns success result

- returns success result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns success result")
val result = VerificationResult.success()
expect result.is_ok()
expect not result.is_err()
```

</details>

#### returns failure result with message

- returns failure result with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns failure result with message")
val result = VerificationResult.failure("Test failed")
expect result.is_err()
expect not result.is_ok()
expect result.unwrap_err() == "Test failed"
```

</details>

#### Argument Matchers - Equality

#### uses eq matcher for exact match

- uses eq matcher for exact match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses eq matcher for exact match")
val matcher = Matcher.eq("hello")
expect matcher.matches("hello")
expect not matcher.matches("world")
```

</details>

#### uses any matcher for wildcard

- uses any matcher for wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses any matcher for wildcard")
val matcher = Matcher.any()
expect matcher.matches("anything")
expect matcher.matches("123")
expect matcher.matches("")
```

</details>

#### Argument Matchers - Numeric

#### uses gt matcher for greater than

- uses gt matcher for greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses gt matcher for greater than")
val matcher = Matcher.gt(10)
expect matcher.matches("15")
expect matcher.matches("100")
expect not matcher.matches("5")
expect not matcher.matches("10")
```

</details>

#### uses lt matcher for less than

- uses lt matcher for less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses lt matcher for less than")
val matcher = Matcher.lt(10)
expect matcher.matches("5")
expect matcher.matches("0")
expect not matcher.matches("10")
expect not matcher.matches("15")
```

</details>

#### uses gte matcher for greater or equal

- uses gte matcher for greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses gte matcher for greater or equal")
val matcher = Matcher.gte(10)
expect matcher.matches("10")
expect matcher.matches("15")
expect not matcher.matches("9")
```

</details>

#### uses lte matcher for less or equal

- uses lte matcher for less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses lte matcher for less or equal")
val matcher = Matcher.lte(10)
expect matcher.matches("10")
expect matcher.matches("5")
expect not matcher.matches("11")
```

</details>

#### Argument Matchers - String Operations

#### uses contains matcher

- uses contains matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses contains matcher")
val matcher = Matcher.contains("error")
expect matcher.matches("fatal error occurred")
expect matcher.matches("error")
expect not matcher.matches("warning")
```

</details>

#### uses starts_with matcher

- uses starts_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses starts_with matcher")
val matcher = Matcher.starts_with("HTTP")
expect matcher.matches("HTTP/1.1")
expect matcher.matches("HTTPS")
expect not matcher.matches("GET HTTP")
```

</details>

#### uses ends_with matcher

- uses ends_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ends_with matcher")
val matcher = Matcher.ends_with(".json")
expect matcher.matches("config.json")
expect matcher.matches("data.json")
expect not matcher.matches("config.yaml")
```

</details>

#### Call Verification

#### verifies no calls were made

- verifies no calls were made


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies no calls were made")
val mock_fn = MockFunction.new("unused")
expect not mock_fn.was_called()
```

</details>

#### verifies single call

- verifies single call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies single call")
val mock_fn = MockFunction.new("called_once")
mock_fn.record_call([])
expect mock_fn.was_called()
expect mock_fn.was_called_n_times(1)
```

</details>

#### verifies specific call count

- verifies specific call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies specific call count")
val mock_fn = MockFunction.new("counter")
mock_fn.record_call([])
mock_fn.record_call([])
mock_fn.record_call([])
expect mock_fn.was_called_n_times(3)
```

</details>

#### gets call by index

- gets call by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets call by index")
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

- gets last call


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets last call")
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

- provides error message for call count mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides error message for call count mismatch")
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

- provides error message for argument mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides error message for argument mismatch")
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

- verifies multiple expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies multiple expectations")
val mock_fn = MockFunction.new("multi")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### resets expectations on reset

- resets expectations on reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets expectations on reset")
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

- handles i64 literal in get_call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles i64 literal in get_call")
val mock_fn = MockFunction.new("literal_test")
mock_fn.record_call(["first"])
mock_fn.record_call(["second"])
# This should work with i64 literal 0
val call = mock_fn.get_call(0)
expect call.is_some()
```

</details>

#### handles i64 literal in array indexing

- handles i64 literal in array indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles i64 literal in array indexing")
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
| Source | `test/01_unit/std/mock_verification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library - Phase 2 (Verification).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b98056bdeefb68ac846167d50ae1ccfac6e05e2835bf6f032230f63c53af7e57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b98056bdeefb68ac846167d50ae1ccfac6e05e2835bf6f032230f63c53af7e57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b98056bdeefb68ac846167d50ae1ccfac6e05e2835bf6f032230f63c53af7e57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/mock_verification_spec.spl
mirror: doc/06_spec/01_unit/std/mock_verification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/mock_verification_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets expectation for call count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_verification_spec.spl:228:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails verification when call count mismatches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/mock_verification_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets expectation for call arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
