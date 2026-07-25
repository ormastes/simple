# Async-Default Function Model

> This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

<!-- sdn-diagram:id=async_default_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_default_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_default_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_default_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async-Default Function Model

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #276-285 |
| Category | Other |
| Status | Draft |
| Type | Extracted Examples (Category B) |
| Reference | async_default.md |
| Source | `test/03_system/feature/language/async_default_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This document specifies Simple's async-default execution model where functions
are async by default and sync is explicit.

Functions without `sync` keyword return `Promise<T>` automatically. The
suspension operator `~=` explicitly marks await points for readability and
control.

## Design Principles

- **Async by default:** No `async` keyword required
- **Explicit suspension:** `~=` shows suspension points
- **Sync when needed:** `sync fn` for synchronous code
- **Type safety:** Promise types automatically inferred

## Syntax

All functions are async by default — no keyword needed:

    fn fetch_user(id: i64) -> User:   # returns Promise<User>
        val data ~= db.query(id)
        User.from(data)

Opt out with `sync` for purely synchronous code:

    sync fn add(a: i64, b: i64) -> i64:
        a + b

Explicit suspension point with `~=`:

    val result ~= expensive_computation()   # suspends; resumes when done

Promise resolved immediately (no I/O):

    val p = Promise.resolved(42)
    p.is_ready()   # => true
    p.get()        # => 42

Chain continuations:

    val doubled = p.map(|v| v * 2)
    doubled.get()  # => 84

## Examples

    # ExecutionMode shows which mode is active
    val mode = ExecutionMode.AsyncDefault
    mode.label()    # => "async-default"

    val sync_mode = ExecutionMode.ExplicitSync
    sync_mode.label()  # => "sync"

    # Promise lifecycle
    val pending = Promise.pending()
    pending.is_ready()   # => false

    val resolved = Promise.resolved(99)
    resolved.is_ready()  # => true
    resolved.get()       # => 99

    # Context carries the active execution mode
    val ctx = AsyncContext.new(ExecutionMode.AsyncDefault)
    ctx.is_async()   # => true

    val sync_ctx = AsyncContext.new(ExecutionMode.ExplicitSync)
    sync_ctx.is_async()  # => false

## Key Concepts

**Async by default** — removing the `async` keyword at every function
declaration reduces boilerplate in codebases where most I/O-bound code is
async. The rare synchronous function opts in with `sync`.

**Promise<T>** — the return type wrapper for async functions. Equivalent to
`Future<T>` in Rust or a `Promise` in JavaScript. Resolved values are
accessed through `.get()`, `~=`, or continuation chaining.

**`~=` at suspension points** — marking await sites explicitly means readers
can scan for `~=` to find all preemption points, simplifying reasoning about
race conditions and cancellation.

**Cancellation safety** — each `~=` site is a safe cancellation point.
Dropping the returned `Promise` cancels the computation at the next
suspension, allowing clean resource release.

**Sync interop** — `sync fn` functions can be called from both sync and async
contexts. Async functions cannot be called from sync functions without an
executor (runtime) to drive them.

**Executor / runtime** — the `simple_runtime::async` module provides a
work-stealing task executor. It schedules coroutines across available threads
and handles I/O readiness notifications from the OS.

## Related Specifications

- **Suspension Operator** - Explicit `~` suspension syntax
- **Concurrency** - Futures, actors, channels
- **Functions** - Function definitions
- **Type System** - Promise type inference

## Scenarios

### Async Default Spec

#### design_overview_3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val promise = Promise.resolved(41)
expect(promise.is_ready()).to_equal(true)
expect(promise.unwrap()).to_equal(41)
```

</details>

#### promise_type_6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapped = Promise.resolved(2).map(_1 + 1)
expect(mapped.is_ready()).to_equal(true)
expect(mapped.unwrap()).to_equal(3)
```

</details>

#### error_handling_36

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val failed = Promise.failed("boom")
expect(failed.is_ready()).to_equal(false)
expect(failed.error_message()).to_equal("boom")
```

</details>

#### examples_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val promise = async_add(2, 3)
expect(promise.is_ready()).to_equal(true)
expect(promise.unwrap()).to_equal(5)
```

</details>

#### motivation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = AsyncContext.new(ExecutionMode.AsyncDefault)
expect(context.mode_name()).to_equal("async-default")
```

</details>

#### syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = sync_add(4, 5)
expect(value).to_equal(9)
```

</details>

#### promise_type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending = make_pending_workflow()
expect(pending.is_ready()).to_equal(false)
```

</details>

#### combinators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Promise.resolved(3).map(_1 * 2).then(Promise.resolved(_1 + 4))
expect(result.is_ready()).to_equal(true)
expect(result.unwrap()).to_equal(10)
```

</details>

#### sync_functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sync_add(10, 1)).to_equal(11)
```

</details>

#### type_inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val promise = Promise.resolved(7)
expect(promise.unwrap()).to_equal(7)
```

</details>

#### effect_inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = AsyncContext.new(ExecutionMode.ExplicitAsync)
expect(context.mode_name()).to_equal("async")
```

</details>

#### interaction_with_suspension

1. var context = AsyncContext new
   - Expected: context.suspended is false
2. context suspend
   - Expected: context.suspended is true
   - Expected: context.current.is_ready() is true
   - Expected: context.current.unwrap() equals `12`
3. context resume
   - Expected: context.suspended is false
   - Expected: context.current.unwrap() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var context = AsyncContext.new(ExecutionMode.AsyncDefault)
expect(context.suspended).to_equal(false)
context.suspend(12)
expect(context.suspended).to_equal(true)
expect(context.current.is_ready()).to_equal(true)
expect(context.current.unwrap()).to_equal(12)
context.resume(99)
expect(context.suspended).to_equal(false)
expect(context.current.unwrap()).to_equal(99)
```

</details>

#### migration_strategy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapped = Promise.resolved(sync_add(6, 7))
expect(wrapped.unwrap()).to_equal(13)
```

</details>

#### examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = Promise.resolved(2).map(_1 + 1).then(Promise.resolved(_1 * 5))
expect(workflow.unwrap()).to_equal(15)
```

</details>

#### promise_type_details

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val failed = Promise.failed("network")
expect(failed.error_message()).to_equal("network")
expect(failed.is_ready()).to_equal(false)
```

</details>

#### performance_considerations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val immediate = complete_workflow(0)
expect(immediate.is_ready()).to_equal(true)
expect(immediate.unwrap()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
