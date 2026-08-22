# mock_verification_spec

> Verifies the mock verification behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_verification_spec

Verifies the mock verification behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_verification_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mock verification behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Mock Library - Phase 2 (Verification)

#### Expectations

#### sets expectation for call count

- Verify: sets expectation for call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: sets expectation for call count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("handler")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails verification when call count mismatches

- Verify: fails verification when call count mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: fails verification when call count mismatches")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("process")
mock_fn.expect_call(3)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### sets expectation for call arguments

- Verify: sets expectation for call arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: sets expectation for call arguments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("save")
mock_fn.expect_call_with(["id_123", "data"])
mock_fn.record_call(["id_123", "data"])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### fails when arguments don't match

- Verify: fails when arguments don't match


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: fails when arguments don't match")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("update")
mock_fn.expect_call_with(["old_value"])
mock_fn.record_call(["new_value"])
val result = mock_fn.verify()
expect result.is_err()
```

</details>

#### VerificationResult

#### returns success result

- Verify: returns success result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: returns success result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = VerificationResult.success()
expect result.is_ok()
expect not result.is_err()
```

</details>

#### returns failure result with message

- Verify: returns failure result with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: returns failure result with message")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = VerificationResult.failure("Test failed")
expect result.is_err()
expect not result.is_ok()
expect result.unwrap_err() == "Test failed"
```

</details>

#### Argument Matchers - Equality

#### uses eq matcher for exact match

- Verify: uses eq matcher for exact match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses eq matcher for exact match")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.eq("hello")
expect matcher.matches("hello")
expect not matcher.matches("world")
```

</details>

#### uses any matcher for wildcard

- Verify: uses any matcher for wildcard


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses any matcher for wildcard")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.any()
expect matcher.matches("anything")
expect matcher.matches("123")
expect matcher.matches("")
```

</details>

#### Argument Matchers - Numeric

#### uses gt matcher for greater than

- Verify: uses gt matcher for greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses gt matcher for greater than")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.gt(10)
expect matcher.matches("15")
expect matcher.matches("100")
expect not matcher.matches("5")
expect not matcher.matches("10")
```

</details>

#### uses lt matcher for less than

- Verify: uses lt matcher for less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses lt matcher for less than")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.lt(10)
expect matcher.matches("5")
expect matcher.matches("0")
expect not matcher.matches("10")
expect not matcher.matches("15")
```

</details>

#### uses gte matcher for greater or equal

- Verify: uses gte matcher for greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses gte matcher for greater or equal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.gte(10)
expect matcher.matches("10")
expect matcher.matches("15")
expect not matcher.matches("9")
```

</details>

#### uses lte matcher for less or equal

- Verify: uses lte matcher for less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses lte matcher for less or equal")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.lte(10)
expect matcher.matches("10")
expect matcher.matches("5")
expect not matcher.matches("11")
```

</details>

#### Argument Matchers - String Operations

#### uses contains matcher

- Verify: uses contains matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses contains matcher")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.contains("error")
expect matcher.matches("fatal error occurred")
expect matcher.matches("error")
expect not matcher.matches("warning")
```

</details>

#### uses starts_with matcher

- Verify: uses starts_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses starts_with matcher")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.starts_with("HTTP")
expect matcher.matches("HTTP/1.1")
expect matcher.matches("HTTPS")
expect not matcher.matches("GET HTTP")
```

</details>

#### uses ends_with matcher

- Verify: uses ends_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: uses ends_with matcher")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val matcher = Matcher.ends_with(".json")
expect matcher.matches("config.json")
expect matcher.matches("data.json")
expect not matcher.matches("config.yaml")
```

</details>

#### Call Verification

#### verifies no calls were made

- Verify: verifies no calls were made


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: verifies no calls were made")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("unused")
expect not mock_fn.was_called()
```

</details>

#### verifies single call

- Verify: verifies single call


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: verifies single call")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("called_once")
mock_fn.record_call([])
expect mock_fn.was_called()
expect mock_fn.was_called_n_times(1)
```

</details>

#### verifies specific call count

- Verify: verifies specific call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: verifies specific call count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("counter")
mock_fn.record_call([])
mock_fn.record_call([])
mock_fn.record_call([])
expect mock_fn.was_called_n_times(3)
```

</details>

#### gets call by index

- Verify: gets call by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: gets call by index")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets last call


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: gets last call")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: provides error message for call count mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: provides error message for call count mismatch")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: provides error message for argument mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: provides error message for argument mismatch")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: verifies multiple expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: verifies multiple expectations")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("multi")
mock_fn.expect_call(2)
mock_fn.record_call([])
mock_fn.record_call([])
val result = mock_fn.verify()
expect result.is_ok()
```

</details>

#### resets expectations on reset

- Verify: resets expectations on reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: resets expectations on reset")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles i64 literal in get_call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: handles i64 literal in get_call")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("literal_test")
mock_fn.record_call(["first"])
mock_fn.record_call(["second"])
# This should work with i64 literal 0
val call = mock_fn.get_call(0)
expect call.is_some()
```

</details>

#### handles i64 literal in array indexing

- Verify: handles i64 literal in array indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_VERIFICATION-001
step("Verify: handles i64 literal in array indexing")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c52ae3aa4671151107503b9fba6f56e410efda4f7578304523e0a077e93efb82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c52ae3aa4671151107503b9fba6f56e410efda4f7578304523e0a077e93efb82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c52ae3aa4671151107503b9fba6f56e410efda4f7578304523e0a077e93efb82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/mock_verification_spec.spl
mirror: doc/06_spec/01_unit/std/mock_verification_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_verification_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/mock_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
