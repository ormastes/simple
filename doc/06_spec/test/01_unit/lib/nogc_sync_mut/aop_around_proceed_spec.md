# Aop Around Proceed Specification

> <details>

<!-- sdn-diagram:id=aop_around_proceed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_around_proceed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_around_proceed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_around_proceed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Around Proceed Specification

## Scenarios

### AOP AroundAdvice with real proceed (E1)

#### handler calls proceed once

#### returns target value and records no denial

- aop clear denials
- var registry = AspectRegistry empty
- fn good around
- registry register around
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `99`
   - Expected: aop_denial_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn good_around(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    val r = proceed()
    r
registry.register_around(make_around("good_around", good_around))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "target_op"), target_fn)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(99)
expect(aop_denial_count()).to_equal(0)
```

</details>

#### handler does not call proceed

#### returns Err and records denial

- aop clear denials
- var registry = AspectRegistry empty
- fn no proceed around
- Ok
- registry register around
   - Expected: result.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `proceed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn no_proceed_around(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    # deliberately skip calling proceed
    Ok(())
registry.register_around(make_around("no_proceed", no_proceed_around))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "skipped_op"), target_fn)
expect(result.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("proceed")).to_equal(true)
```

</details>

#### handler calls proceed twice

#### second proceed call returns Err

- aop clear denials
- var registry = AspectRegistry empty
- fn double proceed
- registry register around
   - Expected: result.is_ok() is true
   - Expected: aop_proceed_double_called() is true
   - Expected: perr contains `more than once`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
# NOTE: nested closures cannot mutate outer locals (read-only capture),
# so the duplicate-call evidence is read back through the module
# accessors aop_proceed_double_called / aop_last_proceed_err.
fn double_proceed(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    val r1 = proceed()
    val r2 = proceed()
    r1
registry.register_around(make_around("double_proceed", double_proceed))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "double_op"), target_fn)
# first proceed succeeded so handler returns Ok; slot is filled
expect(result.is_ok()).to_equal(true)
expect(aop_proceed_double_called()).to_equal(true)
val perr = aop_last_proceed_err()
expect(perr.contains("more than once")).to_equal(true)
```

</details>

#### handler returns Err itself

#### wrap returns Err and denial records that handler failed

- aop clear denials
- var registry = AspectRegistry empty
- fn failing around
- Err
- registry register around
   - Expected: result.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `handler failed after proceed`
   - Expected: denial contains `target ran`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn failing_around(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    val r = proceed()
    Err("handler failed after proceed")
registry.register_around(make_around("failing_around", failing_around))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "fail_op"), target_fn)
expect(result.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("handler failed after proceed")).to_equal(true)
# target ran (proceed was called), so "(target ran)" should appear
expect(denial.contains("target ran")).to_equal(true)
```

</details>

#### multiple AroundAdvices (honest limitation)

#### returns Err and records denial when more than one around advice matches

- aop clear denials
- var registry = AspectRegistry empty
- fn adv a
- proceed
- fn adv b
- proceed
- registry register around
- registry register around
   - Expected: result.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `multiple around advices`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn adv_a(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    proceed()
fn adv_b(ctx: AdviceContext, proceed: fn() -> Result<(), text>) -> Result<(), text>:
    proceed()
registry.register_around(make_around("around_a", adv_a))
registry.register_around(make_around("around_b", adv_b))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "multi_op"), target_fn)
expect(result.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("multiple around advices")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/aop_around_proceed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP AroundAdvice with real proceed (E1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
