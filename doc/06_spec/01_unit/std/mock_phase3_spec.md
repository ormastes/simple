# mock_phase3_spec

> Verifies the mock phase3 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_phase3_spec

Verifies the mock phase3 behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_phase3_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mock phase3 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Mock Library - Phase 3 (Advanced Features)

#### Matcher Composition - AND

#### combines two matchers with AND logic

- Verify: combines two matchers with AND logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: combines two matchers with AND logic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AND fails if either matcher fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: AND fails if either matcher fails")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: combines two matchers with OR logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: combines two matchers with OR logic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m1 = Matcher.eq("user")
val m2 = Matcher.eq("admin")
val combined = Matcher.or_matcher(m1, m2)
expect combined.matches("user")
expect combined.matches("admin")
expect not combined.matches("guest")
```

</details>

#### OR succeeds if either matcher matches

- Verify: OR succeeds if either matcher matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: OR succeeds if either matcher matches")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: negates a matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: negates a matcher")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = Matcher.eq("admin")
val negated = Matcher.not_matcher(m)
expect not negated.matches("admin")
expect negated.matches("user")
expect negated.matches("")
```

</details>

#### NOT inverts boolean logic

- Verify: NOT inverts boolean logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: NOT inverts boolean logic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = Matcher.contains("error")
val negated = Matcher.not_matcher(m)
expect not negated.matches("fatal error")
expect negated.matches("success")
```

</details>

#### Custom Predicate Matchers

#### creates matcher from custom predicate

- Verify: creates matcher from custom predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: creates matcher from custom predicate")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val starts_digit = _1.len() > 0 and _1[0] >= "0" and _1[0] <= "9"
val predicate_m = Matcher.predicate(starts_digit)
expect predicate_m.matches("4abc")
expect predicate_m.matches("100")
expect not predicate_m.matches("abc")
expect not predicate_m.matches("xyz")
```

</details>

#### uses custom predicate for complex logic

- Verify: uses custom predicate for complex logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: uses custom predicate for complex logic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val has_numbers = _1.contains("1") or _1.contains("2") or _1.contains("3")
val pred_m = Matcher.predicate(has_numbers)
expect pred_m.matches("user123")
expect pred_m.matches("abc123")
expect not pred_m.matches("xyz")
```

</details>

#### CallAnalyzer - Call Counting

#### counts calls with specific arguments

- Verify: counts calls with specific arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: counts calls with specific arguments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: returns zero for non-matching calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: returns zero for non-matching calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets first call made


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: gets first call made")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: returns None if no calls made


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: returns None if no calls made")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("unused")
val analyzer = CallAnalyzer.new(mock_fn)
expect analyzer.get_first_call().is_none()
```

</details>

#### CallAnalyzer - Call Range Queries

#### gets calls between indices

- Verify: gets calls between indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: gets calls between indices")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles boundary indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: handles boundary indices")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets calls matching custom predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: gets calls matching custom predicate")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("log")
mock_fn.record_call(["INFO", "Started"])
mock_fn.record_call(["ERROR", "Failed"])
mock_fn.record_call(["INFO", "Completed"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_error = \call:
    call.args.len() > 0 and call.args[0] == "ERROR"
val errors = analyzer.get_calls_matching(has_error)
expect errors.len() == 1
expect errors[0].args[1] == "Failed"
```

</details>

#### returns empty list if no matches

- Verify: returns empty list if no matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: returns empty list if no matches")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("checker")
mock_fn.record_call(["safe"])
mock_fn.record_call(["ok"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_panic = \call:
    call.args.len() > 0 and call.args[0].contains("panic")
val panics = analyzer.get_calls_matching(has_panic)
expect panics.len() == 0
```

</details>

#### SequentialReturns - Basic Usage

#### returns values in sequence

- Verify: returns values in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: returns values in sequence")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: repeats values based on count


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: repeats values based on count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: adds single return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: adds single return value")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val seq = SequentialReturns.new()
seq.add_return_once("only_once")
expect seq.next_value() == Some("only_once")
expect seq.next_value().is_none()
```

</details>

#### chains multiple once calls

- Verify: chains multiple once calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: chains multiple once calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: resets to beginning


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: resets to beginning")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: records method calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: records method calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val spy = Spy.new("user_service")
spy.record_call("get_user", ["id_123"])
spy.record_call("save_user", ["id_456", "John"])
expect spy.total_calls() == 2
expect spy.method_called("get_user")
expect spy.method_called("save_user")
```

</details>

#### tracks method call count

- Verify: tracks method call count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: tracks method call count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: gets all calls to a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: gets all calls to a method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: returns empty list for untracked methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: returns empty list for untracked methods")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val spy = Spy.new("logger")
spy.record_call("info", ["message"])
val debug_calls = spy.get_calls("debug")
expect debug_calls.len() == 0
```

</details>

#### Spy - Method Verification

#### verifies method was called

- Verify: verifies method was called


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: verifies method was called")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val spy = Spy.new("handler")
spy.record_call("process", ["data"])
expect spy.method_called("process")
expect not spy.method_called("cleanup")
```

</details>

#### tracks total calls across all methods

- Verify: tracks total calls across all methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: tracks total calls across all methods")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: generates summary of calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: generates summary of calls")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: combines matcher composition with call analysis


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: combines matcher composition with call analysis")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mock_fn = MockFunction.new("validator")
mock_fn.record_call(["email@test.com"])
mock_fn.record_call(["user123"])
mock_fn.record_call(["admin@test.com"])
val analyzer = CallAnalyzer.new(mock_fn)
val has_email = \call:
    call.args.len() > 0 and call.args[0].contains("@")
val emails = analyzer.get_calls_matching(has_email)
expect emails.len() == 2
val contains_test = Matcher.contains("test")
expect contains_test.matches(emails[0].args[0])
```

</details>

#### uses sequential returns with spy

- Verify: uses sequential returns with spy


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: uses sequential returns with spy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: uses all three matcher composition types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_MOCK_PHASE3-001
step("Verify: uses all three matcher composition types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m_contains_error = Matcher.contains("error")
val m_not_success = Matcher.not_matcher(Matcher.eq("success"))
val m_combined = Matcher.and_matcher(m_contains_error, m_not_success)
expect m_combined.matches("fatal error")
expect not m_combined.matches("success")
expect not m_combined.matches("no problem")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33100ddd9098b47e26feca8bc7c12fe94311f5c32a201aed04fa7e5dcde39af7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33100ddd9098b47e26feca8bc7c12fe94311f5c32a201aed04fa7e5dcde39af7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33100ddd9098b47e26feca8bc7c12fe94311f5c32a201aed04fa7e5dcde39af7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/mock_phase3_spec.spl
mirror: doc/06_spec/01_unit/std/mock_phase3_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/mock_phase3_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/mock_phase3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/mock_phase3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
