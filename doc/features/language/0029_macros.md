# Feature #29: Macros

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #29 |
| **Feature Name** | Macros |
| **Category** | Language |
| **Difficulty** | 5 (Very Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Compile-time code generation with builtin and user-defined macros. Includes vec!, assert!, assert_eq!, format!, panic!, dbg! and custom macro definitions.

## Specification

[doc/spec/metaprogramming.md](../../spec/metaprogramming.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter_macro.rs` | Macro expansion |

## Builtin Macros

| Macro | Purpose |
|-------|---------|
| `vec!(...)` | Create array from elements |
| `assert!(cond)` | Assert condition is true |
| `assert_eq!(a, b)` | Assert values are equal |
| `format!(...)` | Concatenate to string |
| `dbg!(expr)` | Debug print and return |
| `panic!(msg)` | Abort with message |

## User-Defined Macros

```simple
macro name(params) -> (returns result: Type):
    emit result:
        expression
```

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/language/macros_spec.spl` | BDD spec (17 tests) |

## Dependencies

- Depends on: #3
- Required by: None

## Notes

User macros use emit blocks to specify output. Macro hygiene prevents name collisions.
