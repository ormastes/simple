# Feature #43: Futures

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #43 |
| **Feature Name** | Futures |
| **Category** | Concurrency |
| **Difficulty** | 3 (Medium) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Future values representing async computations. Create with future(), resolve with await. Supports eager evaluation and value capture.

## Specification

[doc/spec/concurrency.md](../../spec/concurrency.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/runtime/src/value/async_gen.rs` | Future runtime |
| `src/compiler/src/interpreter.rs` | Interpreter support |

## Syntax

```simple
# Create future from value
let f = future(42)

# Create future from computation
let f = future(expensive_computation())

# Await future to get value
let result = await f

# Await returns immediately for non-futures
let x = await 42  # Returns 42
```

## Multiple Futures

```simple
let f1 = future(task1())
let f2 = future(task2())
let f3 = future(task3())

# Await in any order
let r1 = await f1
let r2 = await f2
let r3 = await f3
```

## Future Semantics

| Behavior | Description |
|----------|-------------|
| Eager evaluation | Futures evaluate when created |
| Await non-future | Returns value immediately |
| Capture | Captures outer variables |
| Order | Can await in any order |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/concurrency/futures_spec.spl` | BDD spec (10 tests) |
| `src/driver/tests/interpreter_async_tests.rs` | Interpreter tests |
| `src/driver/tests/runner_async_tests.rs` | Runner tests |

## Dependencies

- Depends on: None
- Required by: #41

## Notes

Futures evaluate eagerly when created. Await on non-future values returns immediately.
