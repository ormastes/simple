# Interpreter Aop Weave Specification

> Tests covering interp_aop_predicate_matches — execution selector, interp_aop_predicate_matches — combinators, interp_aop_collect — form filtering + pointcut match, interp_aop_sort_by_priority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Aop Weave Specification

## Scenarios

### interp_aop_predicate_matches — execution selector

#### matches exact function name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches exact function name
   - Expected: interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "exact_name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches exact function name")
expect(interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "exact_name")).to_equal(true)
```

</details>

#### does not match a different function name

- does not match a different function name
   - Expected: interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "other_name") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not match a different function name")
expect(interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "other_name")).to_equal(false)
```

</details>

#### matches prefix wildcard

- matches prefix wildcard
   - Expected: interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "handle_request") is true
   - Expected: interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "process_data") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches prefix wildcard")
expect(interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "handle_request")).to_equal(true)
expect(interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "process_data")).to_equal(false)
```

</details>

#### matches suffix wildcard

- matches suffix wildcard
   - Expected: interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_service") is true
   - Expected: interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_controller") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches suffix wildcard")
expect(interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_service")).to_equal(true)
expect(interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_controller")).to_equal(false)
```

</details>

#### matches any function with bare star

- matches any function with bare star
   - Expected: interp_aop_predicate_matches("execution ( * * ( .. ) )", "anything") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches any function with bare star")
expect(interp_aop_predicate_matches("execution ( * * ( .. ) )", "anything")).to_equal(true)
```

</details>

#### keeps advice lookup off shared optional target mutation

- keeps advice lookup off shared optional target mutation
   - Expected: source does not contain `var target: HirFunction? = nil`
   - Expected: source does not contain `target = Some(c)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps advice lookup off shared optional target mutation")
val source = file_read("src/compiler/70.backend/backend/interpreter_aop_weave.spl")

expect(source.contains("var target: HirFunction? = nil")).to_equal(false)
expect(source.contains("target = Some(c)")).to_equal(false)
expect(source).to_contain("var target_index = -1")
expect(source).to_contain("val target = candidates[target_index]")
```

</details>

### interp_aop_predicate_matches — combinators

#### AND requires both sides

- AND requires both sides
   - Expected: interp_aop_predicate_matches(pred, "get_user") is true
   - Expected: interp_aop_predicate_matches(pred, "get_order") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AND requires both sides")
val pred = "execution ( * get* ( .. ) ) & execution ( * *_user ( .. ) )"
expect(interp_aop_predicate_matches(pred, "get_user")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "get_order")).to_equal(false)
```

</details>

#### OR matches either side

- OR matches either side
   - Expected: interp_aop_predicate_matches(pred, "func_a") is true
   - Expected: interp_aop_predicate_matches(pred, "func_b") is true
   - Expected: interp_aop_predicate_matches(pred, "func_c") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("OR matches either side")
val pred = "execution ( * func_a ( .. ) ) | execution ( * func_b ( .. ) )"
expect(interp_aop_predicate_matches(pred, "func_a")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "func_b")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "func_c")).to_equal(false)
```

</details>

#### NOT excludes the matching name

- NOT excludes the matching name
   - Expected: interp_aop_predicate_matches(pred, "should_count") is true
   - Expected: interp_aop_predicate_matches(pred, "should_skip") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("NOT excludes the matching name")
val pred = "! execution ( * should_skip ( .. ) ) & execution ( * should* ( .. ) )"
expect(interp_aop_predicate_matches(pred, "should_count")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "should_skip")).to_equal(false)
```

</details>

#### parenthesized group evaluates before AND

- parenthesized group evaluates before AND
   - Expected: interp_aop_predicate_matches(pred, "a_fn") is true
   - Expected: interp_aop_predicate_matches(pred, "b_fn") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parenthesized group evaluates before AND")
val pred = "( execution ( * a_fn ( .. ) ) | execution ( * b_fn ( .. ) ) ) & ! execution ( * b_fn ( .. ) )"
expect(interp_aop_predicate_matches(pred, "a_fn")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "b_fn")).to_equal(false)
```

</details>

#### unsupported selectors evaluate false without breaking combinators

- unsupported selectors evaluate false without breaking combinators
   - Expected: interp_aop_predicate_matches("attr ( traced )", "traced_operation") is false
   - Expected: interp_aop_predicate_matches(pred, "traced_operation") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsupported selectors evaluate false without breaking combinators")
# attr()/within() are documented follow-ups: parsed, never matched.
expect(interp_aop_predicate_matches("attr ( traced )", "traced_operation")).to_equal(false)
val pred = "execution ( * traced* ( .. ) ) | attr ( traced )"
expect(interp_aop_predicate_matches(pred, "traced_operation")).to_equal(true)
```

</details>

### interp_aop_collect — form filtering + pointcut match

#### collects only advices whose form and pointcut both match

- collects only advices whose form and pointcut both match
   - Expected: before.len() equals `1`
   - Expected: before[0].advice_function equals `before_hit`
   - Expected: after.len() equals `1`
   - Expected: after[0].advice_function equals `after_hit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("collects only advices whose form and pointcut both match")
var advices: [HirAopAdvice] = []
advices = advices.push(mk_advice("execution ( * target ( .. ) )", "before_hit", "before", 10))
advices = advices.push(mk_advice("execution ( * target ( .. ) )", "after_hit", "after_success", 10))
advices = advices.push(mk_advice("execution ( * other ( .. ) )", "before_miss", "before", 10))
val before = interp_aop_collect(advices, "before", "target")
expect(before.len()).to_equal(1)
expect(before[0].advice_function).to_equal("before_hit")
val after = interp_aop_collect(advices, "after_success", "target")
expect(after.len()).to_equal(1)
expect(after[0].advice_function).to_equal("after_hit")
```

</details>

#### returns empty when no pointcut matches

- returns empty when no pointcut matches
   - Expected: got.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty when no pointcut matches")
var advices: [HirAopAdvice] = []
advices = advices.push(mk_advice("execution ( * target ( .. ) )", "h", "before", 10))
val got = interp_aop_collect(advices, "before", "unrelated")
expect(got.len()).to_equal(0)
```

</details>

### interp_aop_sort_by_priority

#### orders highest priority first for before advice

- orders highest priority first for before advice
   - Expected: ordered[0].advice_function equals `high`
   - Expected: ordered[1].advice_function equals `mid`
   - Expected: ordered[2].advice_function equals `low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders highest priority first for before advice")
var advices: [HirAopAdvice] = []
advices = advices.push(mk_advice("*", "low", "before", 1))
advices = advices.push(mk_advice("*", "high", "before", 100))
advices = advices.push(mk_advice("*", "mid", "before", 50))
val ordered = interp_aop_sort_by_priority(advices, true)
expect(ordered[0].advice_function).to_equal("high")
expect(ordered[1].advice_function).to_equal("mid")
expect(ordered[2].advice_function).to_equal("low")
```

</details>

#### orders lowest priority first for after advice

- orders lowest priority first for after advice
   - Expected: ordered[0].advice_function equals `low`
   - Expected: ordered[1].advice_function equals `high`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders lowest priority first for after advice")
var advices: [HirAopAdvice] = []
advices = advices.push(mk_advice("*", "low", "after_success", 1))
advices = advices.push(mk_advice("*", "high", "after_success", 100))
val ordered = interp_aop_sort_by_priority(advices, false)
expect(ordered[0].advice_function).to_equal("low")
expect(ordered[1].advice_function).to_equal("high")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interp_aop_predicate_matches — execution selector, interp_aop_predicate_matches — combinators, interp_aop_collect — form filtering + pointcut match, interp_aop_sort_by_priority.
- interp_aop_predicate_matches — execution selector
- interp_aop_predicate_matches — combinators
- interp_aop_collect — form filtering + pointcut match
- interp_aop_sort_by_priority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fddd2cf86225a828eb05eea8fb15aabf288cedb9cd8680182d641af73153d6e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fddd2cf86225a828eb05eea8fb15aabf288cedb9cd8680182d641af73153d6e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fddd2cf86225a828eb05eea8fb15aabf288cedb9cd8680182d641af73153d6e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/interpreter_aop_weave_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter/interpreter_aop_weave_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/interpreter_aop_weave_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not match a different function name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/interpreter_aop_weave_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches prefix wildcard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
