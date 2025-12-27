# Feature #12: Functions

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #12 |
| **Feature Name** | Functions |
| **Category** | Language / Core |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Functions are the basic unit of code organization in Simple. They support:
- Named functions with `fn` keyword
- Return values with explicit types
- Default argument values
- Named argument calls
- Multiple return values (via tuples)
- Closures and lambdas

## Specification

[spec/functions.md](../../../spec/functions.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter_call.rs` | Function call handling |
| `src/parser/src/parser_impl/items.rs` | Function parsing |
| `src/runtime/src/value/objects.rs` | Runtime function objects |

### Key Components

- **Function Definition**: Syntax and parsing
- **Call Resolution**: Argument matching and binding
- **Closures**: Environment capture
- **FFI**: `rt_closure_*` runtime functions

## Testing

### Simple Tests (BDD)

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/unit/core/functions_spec.spl` | Function behavior tests |

### Rust Tests

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_basic.rs` | Basic function tests |

## Examples

```simple
# Basic function
fn add(a: i64, b: i64) -> i64:
    return a + b

# Default arguments
fn greet(name: str = "World") -> str:
    return f"Hello, {name}!"

# Named arguments
greet(name: "Alice")

# Closure
let adder = fn(x: i64) -> fn(i64) -> i64:
    return fn(y: i64) -> i64:
        return x + y

let add5 = adder(5)
add5(10)  # Returns 15
```

## Dependencies

- Depends on: #10 Basic Types, #11 Variables
- Required by: #15 Classes, #20 Actors, #24 Closures

## Notes

- Functions are first-class values
- Closures capture their lexical environment
- Tail call optimization planned for future
