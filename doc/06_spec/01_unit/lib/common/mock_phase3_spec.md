# Mock Phase3 Specification

> Tests covering Mock Library - Phase 3 (Advanced Features).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Phase3 Specification

## Scenarios

### Mock Library - Phase 3 (Advanced Features)

#### Matcher Composition - AND

#### combines two matchers with AND logic

- combines two matchers with AND logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines two matchers with AND logic")
val m1 = Matcher.gt(5)
val m2 = Matcher.lt(100)
val combined = Matcher.and_matcher(m1, m2)
expect combined.matches("50")
expect combined.matches("10")
expect not combined.matches("2")
expect not combined.matches("150")
```

</details>

#### AND fails if either matcher fails

- AND fails if either matcher fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AND fails if either matcher fails")
val m1 = Matcher.contains("error")
val m2 = Matcher.starts_with("WARN")
val combined = Matcher.and_matcher(m1, m2)
expect not combined.matches("error")
expect not combined.matches("WARNING error")
expect combined.matches("WARN error")
```

</details>

#### Matcher Composition - OR

#### combines two matchers with OR logic

- combines two matchers with OR logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines two matchers with OR logic")
val m1 = Matcher.eq("user")
val m2 = Matcher.eq("admin")
val combined = Matcher.or_matcher(m1, m2)
expect combined.matches("user")
expect combined.matches("admin")
expect not combined.matches("guest")
```

</details>

#### OR succeeds if either matcher matches

- OR succeeds if either matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OR succeeds if either matcher matches")
val m1 = Matcher.contains("GET")
val m2 = Matcher.contains("POST")
val combined = Matcher.or_matcher(m1, m2)
expect combined.matches("GET /users")
expect combined.matches("POST /users")
expect not combined.matches("DELETE /users")
```

</details>

#### Matcher Composition - NOT

#### negates a matcher

- negates a matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates a matcher")
val m = Matcher.eq("admin")
val negated = Matcher.not_matcher(m)
expect not negated.matches("admin")
expect negated.matches("user")
expect negated.matches("")
```

</details>

#### NOT inverts boolean logic

- NOT inverts boolean logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NOT inverts boolean logic")
val m = Matcher.contains("error")
val negated = Matcher.not_matcher(m)
expect not negated.matches("fatal error")
expect negated.matches("success")
```

</details>

#### Custom Predicate Matchers

#### creates matcher from custom predicate

- creates matcher from custom predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates matcher from custom predicate")
val starts_digit = _1.len() > 0 and _1[0] >= "0" and _1[0] <= "9"
val predicate_m = Matcher.predicate(starts_digit)
expect predicate_m.matches("4abc")
expect predicate_m.matches("100")
expect not predicate_m.matches("abc")
expect not predicate_m.matches("xyz")
```

</details>

#### uses custom predicate for complex logic

- uses custom predicate for complex logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses custom predicate for complex logic")
val has_numbers = _1.contains("1") or _1.contains("2") or _1.contains("3")
val pred_m = Matcher.predicate(has_numbers)
expect pred_m.matches("user123")
expect pred_m.matches("abc123")
expect not pred_m.matches("xyz")
```

</details>

#### CallAnalyzer - Call Counting

#### counts calls with specific arguments

- counts calls with specific arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts calls with specific arguments")
val mock_fn = MockFunction.new("service")
mock_fn.record_call(["save", "doc1"])
mock_fn.record_call(["save", "doc1"])
mock_fn.record_call(["save", "doc2"])
val analyzer = CallAnalyzer.new(mock_fn)
expect analyzer.count_calls_with(["save", "doc1"]) == 2
expect analyzer.count_calls_with(["save", "doc2"]) == 1
expect analyzer.count_calls_with(["delete"]) == 0
```

</details>

#### returns zero for non-matching calls

- returns zero for non-matching calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero for non-matching calls")
val mock_fn = MockFunction.new("handler")
mock_fn.record_call(["init"])
mock_fn.record_call(["start"])
val analyzer = CallAnalyzer.new(mock_fn)
expect analyzer.count_calls_with(["stop"]) == 0
expect analyzer.count_calls_with(["cleanup"]) == 0
```

</details>

#### CallAnalyzer - Pattern Matching

#### gets first call made

- gets first call made


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets first call made")
val mock_fn = MockFunction.new("sequence")
mock_fn.record_call(["first"])
mock_fn.record_call(["second"])
mock_fn.record_call(["third"])
val analyzer = CallAnalyzer.new(mock_fn)
val first = analyzer.get_first_call()
expect first.is_some()
match first:
    Some(call): expect call.args[0] == "first"
    None: fail "Should have first call"
```

</details>

#### returns None if no calls made

- returns None if no calls made


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None if no calls made")
val mock_fn = MockFunction.new("unused")
val analyzer = CallAnalyzer.new(mock_fn)
expect analyzer.get_first_call().is_none()
```

</details>

#### CallAnalyzer - Call Range Queries

#### gets calls between indices

- gets calls between indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets calls between indices")
val mock_fn = MockFunction.new("api")
mock_fn.record_call(["call0"])
mock_fn.record_call(["call1"])
mock_fn.record_call(["call2"])
mock_fn.record_call(["call3"])
mock_fn.record_call(["call4"])
val analyzer = CallAnalyzer.new(mock_fn)
val range = analyzer.get_calls_between(start_idx=1, end_idx=4)
expect range.len() == 3
expect range[0].args[0] == "call1"
expect range[1].args[0] == "call2"
expect range[2].args[0] == "call3"
```

</details>

#### handles boundary indices

- handles boundary indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles boundary indices")
val mock_fn = MockFunction.new("bounded")
mock_fn.record_call(["a"])
mock_fn.record_call(["b"])
mock_fn.record_call(["c"])
val analyzer = CallAnalyzer.new(mock_fn)
val range = analyzer.get_calls_between(start_idx=0, end_idx=3)
expect range.len() == 3
```

</details>

#### CallAnalyzer - Predicate Matching

#### gets calls matching custom predicate

- gets calls matching custom predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets calls matching custom predicate")
val mock_fn = MockFunction.new("log")
mock_fn.record_call(["INFO", "Started"])
mock_fn.record_call(["ERROR", "Failed"])
mock_fn.record_call(["INFO", "Completed"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_error = \call:
    var ca = call.args
    ca.len() > 0 and ca[0] == "ERROR"
val errors = analyzer.get_calls_matching(has_error)
expect errors.len() == 1
var err0 = errors[0]
var err0args = err0.args
expect err0args[1] == "Failed"
```

</details>

#### returns empty list if no matches

- returns empty list if no matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list if no matches")
val mock_fn = MockFunction.new("checker")
mock_fn.record_call(["safe"])
mock_fn.record_call(["ok"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_panic = \call:
    var ca = call.args
    ca.len() > 0 and ca[0].contains("panic")
val panics = analyzer.get_calls_matching(has_panic)
expect panics.len() == 0
```

</details>

#### SequentialReturns - Basic Usage

#### returns values in sequence

- returns values in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns values in sequence")
val seq = SequentialReturns.new()
seq.add_return("first", 1)
seq.add_return("second", 1)
seq.add_return("third", 1)
expect seq.next_value() == Some("first")
expect seq.next_value() == Some("second")
expect seq.next_value() == Some("third")
expect seq.next_value().is_none()
```

</details>

#### repeats values based on count

- repeats values based on count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats values based on count")
val seq = SequentialReturns.new()
seq.add_return("value_a", 3)
seq.add_return("value_b", 2)
expect seq.next_value() == Some("value_a")
expect seq.next_value() == Some("value_a")
expect seq.next_value() == Some("value_a")
expect seq.next_value() == Some("value_b")
expect seq.next_value() == Some("value_b")
expect seq.next_value().is_none()
```

</details>

#### SequentialReturns - add_return_once

#### adds single return value

- adds single return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds single return value")
val seq = SequentialReturns.new()
seq.add_return_once("only_once")
expect seq.next_value() == Some("only_once")
expect seq.next_value().is_none()
```

</details>

#### chains multiple once calls

- chains multiple once calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains multiple once calls")
val seq = SequentialReturns.new()
seq.add_return_once("alpha")
seq.add_return_once("beta")
seq.add_return_once("gamma")
expect seq.next_value() == Some("alpha")
expect seq.next_value() == Some("beta")
expect seq.next_value() == Some("gamma")
expect seq.next_value().is_none()
```

</details>

#### SequentialReturns - Reset

#### resets to beginning

- resets to beginning


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets to beginning")
val seq = SequentialReturns.new()
seq.add_return_once("first")
seq.add_return_once("second")
expect seq.next_value() == Some("first")
expect seq.next_value() == Some("second")
seq.reset()
expect seq.next_value() == Some("first")
expect seq.next_value() == Some("second")
```

</details>

#### Spy - Basic Call Recording

#### records method calls

- records method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records method calls")
val spy = Spy.new("user_service")
spy.record_call("get_user", ["id_123"])
spy.record_call("save_user", ["id_456", "John"])
expect spy.total_calls() == 2
expect spy.method_called("get_user")
expect spy.method_called("save_user")
```

</details>

#### tracks method call count

- tracks method call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks method call count")
val spy = Spy.new("cache")
spy.record_call("get", ["key1"])
spy.record_call("get", ["key2"])
spy.record_call("get", ["key3"])
spy.record_call("set", ["key", "value"])
expect spy.method_call_count("get") == 3
expect spy.method_call_count("set") == 1
expect spy.method_call_count("delete") == 0
```

</details>

#### Spy - Call Retrieval

#### gets all calls to a method

- gets all calls to a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets all calls to a method")
val spy = Spy.new("database")
spy.record_call("query", ["SELECT", "users"])
spy.record_call("query", ["SELECT", "posts"])
spy.record_call("execute", ["INSERT"])
val queries = spy.get_calls("query")
expect queries.len() == 2
expect queries[0].args[1] == "SELECT"
expect queries[1].args[1] == "SELECT"
```

</details>

#### returns empty list for untracked methods

- returns empty list for untracked methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list for untracked methods")
val spy = Spy.new("logger")
spy.record_call("info", ["message"])
val debug_calls = spy.get_calls("debug")
expect debug_calls.len() == 0
```

</details>

#### Spy - Method Verification

#### verifies method was called

- verifies method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies method was called")
val spy = Spy.new("handler")
spy.record_call("process", ["data"])
expect spy.method_called("process")
expect not spy.method_called("cleanup")
```

</details>

#### tracks total calls across all methods

- tracks total calls across all methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks total calls across all methods")
val spy = Spy.new("api")
spy.record_call("GET", [])
spy.record_call("POST", [])
spy.record_call("PUT", [])
spy.record_call("DELETE", [])
expect spy.total_calls() == 4
```

</details>

#### Spy - Summary

#### generates summary of calls

- generates summary of calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates summary of calls")
val spy = Spy.new("test_spy")
spy.record_call("init", [])
spy.record_call("process", ["data"])
val summary = spy.summary()
expect summary.contains("test_spy")
expect summary.contains("2")
```

</details>

#### Complex Scenarios

#### combines matcher composition with call analysis

- combines matcher composition with call analysis


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines matcher composition with call analysis")
val mock_fn = MockFunction.new("validator")
mock_fn.record_call(["email@test.com"])
mock_fn.record_call(["user123"])
mock_fn.record_call(["admin@test.com"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_email = \call:
    var ca = call.args
    ca.len() > 0 and ca[0].contains("@")
val emails = analyzer.get_calls_matching(has_email)
expect emails.len() == 2
val contains_test = Matcher.contains("test")
var em0 = emails[0]
var em0args = em0.args
expect contains_test.matches(em0args[0])
```

</details>

#### uses sequential returns with spy

- uses sequential returns with spy


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses sequential returns with spy")
val seq = SequentialReturns.new()
seq.add_return("initialized", 1)
seq.add_return("processing", 2)
seq.add_return("completed", 1)
val spy = Spy.new("workflow")
spy.record_call("status", [])
spy.record_call("status", [])
spy.record_call("status", [])
spy.record_call("status", [])
expect spy.method_call_count("status") == 4
expect spy.total_calls() == 4
```

</details>

#### uses all three matcher composition types

- uses all three matcher composition types


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses all three matcher composition types")
val m_contains_error = Matcher.contains("error")
val m_not_success = Matcher.not_matcher(Matcher.eq("success"))
val m_combined = Matcher.and_matcher(m_contains_error, m_not_success)
expect m_combined.matches("fatal error")
expect not m_combined.matches("success")
expect not m_combined.matches("no problem")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mock_phase3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock Library - Phase 3 (Advanced Features).
- Mock Library - Phase 3 (Advanced Features)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `0530d0b82f052c0c8d237a0da6bdbdebc4c9f67b4684d2b6dccf1ea764a192a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0530d0b82f052c0c8d237a0da6bdbdebc4c9f67b4684d2b6dccf1ea764a192a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0530d0b82f052c0c8d237a0da6bdbdebc4c9f67b4684d2b6dccf1ea764a192a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/mock_phase3_spec.spl
mirror: doc/06_spec/01_unit/lib/common/mock_phase3_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/mock_phase3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/mock_phase3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/mock_phase3_spec.spl:288:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'combines two matchers with AND logic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_phase3_spec.spl:299:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AND fails if either matcher fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mock_phase3_spec.spl:310:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'combines two matchers with OR logic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
