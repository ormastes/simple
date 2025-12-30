# Feature #12: Functions

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #12 |
| **Feature Name** | Functions |
| **Category** | Language |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

First-class functions with lexical closure. Supports named functions, anonymous lambdas, default parameters, variadic arguments, and higher-order functions like map/filter/reduce.

## Specification

[doc/spec/functions.md](../../doc/spec/functions.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter_call.rs` | Implementation |
| `src/parser/src/expressions/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_basic_tests.rs` | Test suite |

## Examples

```simple
# Named function
fn greet(name: String) -> String:
    return "Hello, " + name + "!"

# Lambda expression
let double = \x: x * 2

# Higher-order functions
let evens = [1,2,3,4].filter(\x: x % 2 == 0)
```

## Dependencies

- Depends on: #1, #2
- Required by: #11

## Notes

Functions are first-class values. Closures capture lexical environment.
