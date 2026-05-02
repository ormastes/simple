# Async-Default Function Model

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #276-285 |
| Status | Draft |
| Type | Extracted Examples (Category B) |
| Reference | async_default.md |
| Source | `test/specs/async_default_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** async, sync, effects, promises, futures
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects
**Symbols:** Promise, Suspension, ExecutionMode, AsyncContext, Future
**Module:** simple_runtime::async
**Migrated From:** doc/06_spec/async_default.md

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

    val mode = ExecutionMode.AsyncDefault
    mode.label()    # => "async-default"

    val sync_mode = ExecutionMode.ExplicitSync
    sync_mode.label()  # => "sync"

    val pending = Promise.pending()
    pending.is_ready()   # => false

    val resolved = Promise.resolved(99)
    resolved.is_ready()  # => true
    resolved.get()       # => 99

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/async_default/summary.txt` |

## Scenarios

- design_overview_3
- promise_type_6
- error_handling_36
- examples_32
- motivation
- syntax
- promise_type
- combinators
- sync_functions
- type_inference
- effect_inference
- interaction_with_suspension
- migration_strategy
- examples
- promise_type_details
- performance_considerations
