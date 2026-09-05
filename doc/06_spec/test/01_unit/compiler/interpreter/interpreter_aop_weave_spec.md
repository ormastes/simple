# Interpreter Aop Weave Specification

> <details>

<!-- sdn-diagram:id=interpreter_aop_weave_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_aop_weave_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_aop_weave_spec -> std
interpreter_aop_weave_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_aop_weave_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Aop Weave Specification

## Scenarios

### interp_aop_predicate_matches — execution selector

#### matches exact function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "exact_name")).to_equal(true)
```

</details>

#### does not match a different function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(interp_aop_predicate_matches("execution ( * exact_name ( .. ) )", "other_name")).to_equal(false)
```

</details>

#### matches prefix wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "handle_request")).to_equal(true)
expect(interp_aop_predicate_matches("execution ( * handle* ( .. ) )", "process_data")).to_equal(false)
```

</details>

#### matches suffix wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_service")).to_equal(true)
expect(interp_aop_predicate_matches("execution ( * *_service ( .. ) )", "user_controller")).to_equal(false)
```

</details>

#### matches any function with bare star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(interp_aop_predicate_matches("execution ( * * ( .. ) )", "anything")).to_equal(true)
```

</details>

#### keeps advice lookup off shared optional target mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/70.backend/backend/interpreter_aop_weave.spl")

expect(source.contains("var target: HirFunction? = nil")).to_equal(false)
expect(source.contains("target = Some(c)")).to_equal(false)
expect(source).to_contain("var target_index = -1")
expect(source).to_contain("val target = candidates[target_index]")
```

</details>

### interp_aop_predicate_matches — combinators

#### AND requires both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "execution ( * get* ( .. ) ) & execution ( * *_user ( .. ) )"
expect(interp_aop_predicate_matches(pred, "get_user")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "get_order")).to_equal(false)
```

</details>

#### OR matches either side

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "execution ( * func_a ( .. ) ) | execution ( * func_b ( .. ) )"
expect(interp_aop_predicate_matches(pred, "func_a")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "func_b")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "func_c")).to_equal(false)
```

</details>

#### NOT excludes the matching name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "! execution ( * should_skip ( .. ) ) & execution ( * should* ( .. ) )"
expect(interp_aop_predicate_matches(pred, "should_count")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "should_skip")).to_equal(false)
```

</details>

#### parenthesized group evaluates before AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = "( execution ( * a_fn ( .. ) ) | execution ( * b_fn ( .. ) ) ) & ! execution ( * b_fn ( .. ) )"
expect(interp_aop_predicate_matches(pred, "a_fn")).to_equal(true)
expect(interp_aop_predicate_matches(pred, "b_fn")).to_equal(false)
```

</details>

#### unsupported selectors evaluate false without breaking combinators

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# attr()/within() are documented follow-ups: parsed, never matched.
expect(interp_aop_predicate_matches("attr ( traced )", "traced_operation")).to_equal(false)
val pred = "execution ( * traced* ( .. ) ) | attr ( traced )"
expect(interp_aop_predicate_matches(pred, "traced_operation")).to_equal(true)
```

</details>

### interp_aop_collect — form filtering + pointcut match

#### collects only advices whose form and pointcut both match

- advices = advices push
- advices = advices push
- advices = advices push
   - Expected: before.len() equals `1`
   - Expected: before[0].advice_function equals `before_hit`
   - Expected: after.len() equals `1`
   - Expected: after[0].advice_function equals `after_hit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- advices = advices push
   - Expected: got.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var advices: [HirAopAdvice] = []
advices = advices.push(mk_advice("execution ( * target ( .. ) )", "h", "before", 10))
val got = interp_aop_collect(advices, "before", "unrelated")
expect(got.len()).to_equal(0)
```

</details>

### interp_aop_sort_by_priority

#### orders highest priority first for before advice

- advices = advices push
- advices = advices push
- advices = advices push
   - Expected: ordered[0].advice_function equals `high`
   - Expected: ordered[1].advice_function equals `mid`
   - Expected: ordered[2].advice_function equals `low`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- advices = advices push
- advices = advices push
   - Expected: ordered[0].advice_function equals `low`
   - Expected: ordered[1].advice_function equals `high`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
