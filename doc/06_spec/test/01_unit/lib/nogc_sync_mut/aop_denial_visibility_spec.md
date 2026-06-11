# Aop Denial Visibility Specification

> <details>

<!-- sdn-diagram:id=aop_denial_visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_denial_visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_denial_visibility_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_denial_visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Denial Visibility Specification

## Scenarios

### AOP advice denial visibility (H10)

#### before advice denies

#### returns Err and records the denial

- aop clear denials
- var registry = AspectRegistry empty
- registry register
   - Expected: result.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `before`
   - Expected: denial contains `guarded_op`
   - Expected: denial contains `denied by policy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
registry.register(make_aspect("deny_before", AdviceKind.Before, deny_handler))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "guarded_op"), target_fn)
expect(result.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("before")).to_equal(true)
expect(denial.contains("guarded_op")).to_equal(true)
expect(denial.contains("denied by policy")).to_equal(true)
```

</details>

#### around advice denies

#### records denial tagged as around

- aop clear denials
- var registry = AspectRegistry empty
- registry register
   - Expected: result.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `around`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
registry.register(make_aspect("deny_around", AdviceKind.Around, deny_handler))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "wrapped_op"), target_fn)
expect(result.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("around")).to_equal(true)
```

</details>

#### advice allows

#### runs the join point and records nothing

- aop clear denials
- var registry = AspectRegistry empty
- registry register
   - Expected: result.is_ok() is true
   - Expected: result.unwrap() equals `42`
   - Expected: aop_denial_count() equals `0`
   - Expected: aop_last_denial() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
registry.register(make_aspect("allow_all", AdviceKind.Before, allow_handler))
val weaver = AspectWeaver.with_registry(registry)
val result = weaver.wrap(JoinPoint.FunctionCall(name: "open_op"), target_fn)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(42)
expect(aop_denial_count()).to_equal(0)
expect(aop_last_denial()).to_equal("")
```

</details>

#### denials accumulate

#### counts each skipped join point

- aop clear denials
- var registry = AspectRegistry empty
- registry register
   - Expected: r1.is_err() is true
   - Expected: r2.is_err() is true
   - Expected: aop_denial_count() equals `2`
   - Expected: denial contains `op_two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
registry.register(make_aspect("deny_before", AdviceKind.Before, deny_handler))
val weaver = AspectWeaver.with_registry(registry)
val r1 = weaver.wrap(JoinPoint.FunctionCall(name: "op_one"), target_fn)
val r2 = weaver.wrap(JoinPoint.FunctionCall(name: "op_two"), target_fn)
expect(r1.is_err()).to_equal(true)
expect(r2.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(2)
val denial = aop_last_denial()
expect(denial.contains("op_two")).to_equal(true)
```

</details>

#### clear resets bookkeeping

#### zeroes count and clears last denial

- aop clear denials
- var registry = AspectRegistry empty
- registry register
   - Expected: r.is_err() is true
- aop clear denials
   - Expected: aop_denial_count() equals `0`
   - Expected: aop_last_denial() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
registry.register(make_aspect("deny_before", AdviceKind.Before, deny_handler))
val weaver = AspectWeaver.with_registry(registry)
val r = weaver.wrap(JoinPoint.FunctionCall(name: "op"), target_fn)
expect(r.is_err()).to_equal(true)
aop_clear_denials()
expect(aop_denial_count()).to_equal(0)
expect(aop_last_denial()).to_equal("")
```

</details>

#### after-denial marker (E2)

#### denial message contains target-executed when after advice denies

- aop clear denials
- var registry = AspectRegistry empty
- fn after deny
- Err
- registry register
   - Expected: r.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `target-executed`
   - Expected: denial contains `after_op`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn after_deny(ctx: AdviceContext) -> Result<(), text>:
    Err("after policy blocked")
registry.register(make_aspect("deny_after", AdviceKind.After, after_deny))
val weaver = AspectWeaver.with_registry(registry)
val r = weaver.wrap(JoinPoint.FunctionCall(name: "after_op"), target_fn)
expect(r.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("target-executed")).to_equal(true)
expect(denial.contains("after_op")).to_equal(true)
```

</details>

#### legacy around pre-hook still works (E1 backward compat)

#### old-style Around via Advice struct runs as pre-hook

- aop clear denials
- var registry = AspectRegistry empty
- fn around deny
- Err
- registry register
   - Expected: r.is_err() is true
   - Expected: aop_denial_count() equals `1`
   - Expected: denial contains `around`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
aop_clear_denials()
var registry = AspectRegistry.empty()
fn around_deny(ctx: AdviceContext) -> Result<(), text>:
    Err("old-style around denied")
registry.register(make_aspect("legacy_around", AdviceKind.Around, around_deny))
val weaver = AspectWeaver.with_registry(registry)
val r = weaver.wrap(JoinPoint.FunctionCall(name: "legacy_op"), target_fn)
expect(r.is_err()).to_equal(true)
expect(aop_denial_count()).to_equal(1)
val denial = aop_last_denial()
expect(denial.contains("around")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/aop_denial_visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP advice denial visibility (H10)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
