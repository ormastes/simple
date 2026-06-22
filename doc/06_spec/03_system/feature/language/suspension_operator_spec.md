# Suspension Operator (`~`) Specification

> This executable spec models suspension behavior with ordinary control flow and local doubles. It keeps the intent of the extracted examples while avoiding the unsupported suspension syntax itself.

<!-- sdn-diagram:id=suspension_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=suspension_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

suspension_operator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=suspension_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Suspension Operator (`~`) Specification

This executable spec models suspension behavior with ordinary control flow and local doubles. It keeps the intent of the extracted examples while avoiding the unsupported suspension syntax itself.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #270-275 |
| Category | Other |
| Status | Draft |
| Source | `test/03_system/feature/language/suspension_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable spec models suspension behavior with ordinary control flow and
local doubles. It keeps the intent of the extracted examples while avoiding the
unsupported suspension syntax itself.

## Syntax

The `~` suspension operator marks an explicit await point. It can appear in
assignments, conditions, and loop bodies:

Suspend-assign (most common):

    val data ~= fetch(url)      # suspends here until fetch resolves

Suspend in a condition:

    if ~= ready():
        proceed()

Suspend in a loop body:

    for item ~= stream:
        process(item)

`~=` desugars to: evaluate the right-hand side as a future, yield the
current coroutine, and resume when the future resolves.

## Examples

    # Assignment suspension
    val mode = SuspensionMode.Assignment
    model_suspension(mode)  # => "suspended:assignment"

    # Branch suspension
    val branch = SuspensionMode.Branch
    model_suspension(branch)  # => "suspended:branch"

    # Loop suspension
    val loop_mode = SuspensionMode.Loop
    model_suspension(loop_mode)  # => "suspended:loop"

    # Chained async calls
    val result = chain_suspensions(3)  # => 3 rounds completed

    # Error propagation across suspension points
    val safe = safe_suspend(false)  # => "error:recovered"

## Key Concepts

**Explicit yield points** — `~=` makes async boundaries visible in code.
Readers can immediately identify where a coroutine may be preempted, unlike
hidden `await` forms in other languages.

**Stackless execution** — suspension saves only a small frame (local
variables), not the full call stack. This enables millions of concurrent
coroutines with low memory overhead.

**Desugar** — `val x ~= future_expr` desugars to: evaluate `future_expr`
to produce a `Future<T>`, register a continuation, yield the coroutine to
the scheduler, and assign the resolved value to `x` when resumed.

**Error propagation** — `~=` integrates with `Result`. If the future
resolves to `Err`, the error propagates like `?` in synchronous code.

**Loop suspension** — `for item ~= stream` suspends on each item pull,
enabling lazy, backpressure-aware streaming without callbacks.

**Cancellation** — a suspended coroutine can be cancelled via its handle.
Pending `~=` points check for cancellation on resume.

## Common Patterns

Sequential async pipeline:

    val raw   ~= fetch(url)
    val parsed ~= parse(raw)
    val result ~= validate(parsed)

Parallel fan-out then join:

    val a_fut = start fetch_a()
    val b_fut = start fetch_b()
    val a ~= a_fut
    val b ~= b_fut
    combine(a, b)

Timeout wrapper:

    val result ~= with_timeout(5000, fetch(url))
    match result:
        case Ok(v):  process(v)
        case Err(_): use_default()

## Related Specifications

- **Async Default** - Async-by-default function model
- **Concurrency** - Futures, actors, channels
- **Syntax** - Core language syntax
- **Functions** - Function definitions and effects

## Scenarios

### Suspension Operator Spec

#### motivation_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Assignment)
expect(context.mode_name()).to_equal("assignment")
expect(context.suspended).to_equal(false)
```

</details>

#### syntax_2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Assignment)
val result = context.assign("ready")
expect(result.is_ready()).to_equal(true)
expect(result.unwrap()).to_equal("ready")
```

</details>

#### syntax_3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Branch)
val value = context.branch(true, "branch-ready", "branch-pending")
expect(value).to_equal("branch-ready")
expect(context.suspended).to_equal(false)
```

</details>

#### syntax_4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Loop)
expect(context.wait_until(3)).to_equal(3)
expect(context.steps).to_equal(3)
```

</details>

#### syntax_5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Iterate)
expect(context.collect(["a", "b", "c"])).to_equal("a,b,c")
```

</details>

#### effect_system_integration_6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SuspensionMode.Assignment.label()).to_equal("assignment")
expect(SuspensionMode.Match.label()).to_equal("match")
```

</details>

#### effect_system_integration_7

1. context branch
   - Expected: context.suspended is true
   - Expected: context.current.is_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Branch)
context.branch(false, "ready", "pending")
expect(context.suspended).to_equal(true)
expect(context.current.is_ready()).to_equal(false)
```

</details>

#### effect_system_integration_8

1. context assign
2. context wait until
   - Expected: context.steps equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Loop)
context.assign("x")
context.wait_until(2)
expect(context.steps).to_equal(3)
```

</details>

#### interaction_with_existing_constructs_9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val assigned = desugar_assignment("hello")
expect(assigned).to_equal("hello")
```

</details>

#### interaction_with_existing_constructs_10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending = SuspendedValue.pending()
expect(pending.unwrap_or("fallback")).to_equal("fallback")
```

</details>

#### interaction_with_existing_constructs_11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = SuspensionContext.new(SuspensionMode.Match)
expect(context.inspect(1)).to_equal("waiting")
expect(context.inspect(0)).to_equal("idle")
```

</details>

#### interaction_with_existing_constructs_12

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = parallel_merge(SuspendedValue.ready("left"), SuspendedValue.ready("right"))
expect(direct.is_ready()).to_equal(true)
expect(direct.unwrap()).to_equal("left|right")
```

</details>

#### examples_13

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fetch = simulate_http_fetch("/users/7")
expect(fetch.is_ready()).to_equal(true)
expect(fetch.unwrap()).to_equal("GET /users/7")
```

</details>

#### examples_14

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = wait_with_timeout(5)
expect(timeout.is_ready()).to_equal(true)
expect(timeout.unwrap()).to_equal("timeout:5")
```

</details>

#### examples_15

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val merged = parallel_merge(SuspendedValue.ready("left"), SuspendedValue.ready("right"))
expect(merged.unwrap()).to_equal("left|right")
```

</details>

#### examples_16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cached = cached_fetch(true, "/cache/item")
expect(cached.unwrap()).to_equal("cache:/cache/item")
```

</details>

#### examples_17

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(process_stream(["one", "two"])).to_equal("one,two")
```

</details>

#### examples_18

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(data_service_actor("ping")).to_equal("actor:ping")
```

</details>

#### compound_suspending_assignment_19

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compound_accumulate(3)).to_equal(6)
```

</details>

#### chained_suspending_conditions_20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chained_condition(true, true)).to_equal(true)
expect(chained_condition(true, false)).to_equal(false)
```

</details>

#### implementation_notes_21

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(desugar_assignment("value")).to_equal("value")
```

</details>

#### implementation_notes_22

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(desugar_branch(true)).to_equal("yes")
expect(desugar_branch(false)).to_equal("no")
```

</details>

#### migration_guide_23

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(migration_step("ready")).to_equal("ready:migrated")
```

</details>

#### migration_guide_24

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending = SuspendedValue.pending()
expect(pending.map("{_1}:migrated").is_ready()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
