# Suspension Operator (`~`) Specification

This executable spec models suspension behavior with ordinary control flow and local doubles. It keeps the intent of the extracted examples while avoiding the unsupported suspension syntax itself.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #270-275 |
| Status | Draft |
| Source | `test/specs/suspension_operator_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** async, suspension, await, effects, concurrency
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects
**Migrated From:** doc/06_spec/suspension_operator.md

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

    val mode = SuspensionMode.Assignment
    model_suspension(mode)  # => "suspended:assignment"

    val branch = SuspensionMode.Branch
    model_suspension(branch)  # => "suspended:branch"

    val loop_mode = SuspensionMode.Loop
    model_suspension(loop_mode)  # => "suspended:loop"

    val result = chain_suspensions(3)  # => 3 rounds completed

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/suspension_operator/summary.txt` |

## Scenarios

- motivation_1
- syntax_2
- syntax_3
- syntax_4
- syntax_5
- effect_system_integration_6
- effect_system_integration_7
- effect_system_integration_8
- interaction_with_existing_constructs_9
- interaction_with_existing_constructs_10
- interaction_with_existing_constructs_11
- interaction_with_existing_constructs_12
- examples_13
- examples_14
- examples_15
- examples_16
- examples_17
- examples_18
- compound_suspending_assignment_19
- chained_suspending_conditions_20
- implementation_notes_21
- implementation_notes_22
- migration_guide_23
- migration_guide_24
