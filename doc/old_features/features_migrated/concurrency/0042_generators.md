# Feature #42: Generators

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #42 |
| **Feature Name** | Generators |
| **Category** | Concurrency |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Generators for lazy value production using yield. Supports single and multiple yields, state preservation, captured variables, and collection.

## Specification

[doc/spec/concurrency.md](../../spec/concurrency.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/mir/generator.rs` | Generator lowering |
| `src/runtime/src/value/async_gen.rs` | Generator runtime |

## Syntax

```simple
# Create generator with yield
let gen = generator(\: yield 42)

# Get next value
let value = next(gen)

# Multiple yields
let gen = generator(\: [yield 1, yield 2, yield 3])

# Collect all values
let arr = collect(gen)
```

## Yield Precedence

Yield has low precedence. Use parentheses for expressions:
```simple
yield (x + 1)    # Correct
yield x + 1      # May not work as expected
```

## Generator Operations

| Operation | Description |
|-----------|-------------|
| `generator(\: ...)` | Create generator |
| `next(gen)` | Get next value |
| `collect(gen)` | Collect all values |

## State Machine

Generators are lowered to state machines:
- Dispatcher block for state routing
- Resume blocks for each yield point
- Frame for preserved local variables

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/concurrency/generators_spec.spl` | BDD spec (12 tests) |
| `src/driver/tests/interpreter_async_tests.rs` | Interpreter tests |
| `src/driver/tests/runner_async_tests.rs` | Runner tests |

## Dependencies

- Depends on: #24
- Required by: None

## Notes

Generators use state machine lowering in MIR. Yield has low precedence - use parentheses for expressions.
