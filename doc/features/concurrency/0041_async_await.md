# Feature #41: Async/Await

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #41 |
| **Feature Name** | Async/Await |
| **Category** | Concurrency |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Async functions for non-blocking computation. Includes async fn declarations, effect checking for blocking operations, and await for future resolution.

## Specification

[doc/spec/concurrency.md](../../spec/concurrency.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/effects.rs` | Effect checking |
| `src/runtime/src/value/async_gen.rs` | Async runtime |

## Syntax

```simple
# Async function declaration
async fn compute(x):
    return x * 2

# Create and await future
let f = future(expensive_computation())
let result = await f

# Await async function directly
let value = await fetch_data()
```

## Effect Checking

Async functions cannot use blocking operations:
- No `print()` or I/O in async fn
- No `await` inside async fn body
- Effect system enforces at compile time

## Async Patterns

| Pattern | Example |
|---------|---------|
| Basic async | `async fn compute(x): return x * 2` |
| Chained async | `async fn chain(x): return await other(x)` |
| Future creation | `let f = future(value)` |
| Await resolution | `let v = await f` |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/concurrency/async_await_spec.spl` | BDD spec (10 tests) |
| `src/driver/tests/interpreter_async_tests.rs` | Interpreter tests |
| `src/driver/tests/runner_async_tests.rs` | Runner tests |

## Dependencies

- Depends on: #12, #43
- Required by: None

## Notes

Async functions cannot use blocking operations like print or await. Effect system enforces async safety at compile time.
