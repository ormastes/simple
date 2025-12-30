# Feature #32: Generics

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #32 |
| **Feature Name** | Generics |
| **Category** | Types |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Generic type parameters for functions, structs, and enums. Supports single and multiple type parameters with bracket notation.

## Specification

[doc/spec/types.md](../../spec/types.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/hir/types.rs` | Generic type handling |
| `src/type/src/lib.rs` | Type inference |

## Syntax

```simple
# Generic function
fn identity<T>(x: T) -> T:
    return x

# Generic struct
struct Box<T>:
    value: T

# Generic enum
enum Maybe<T>:
    Just(T)
    Nothing

# Type arguments use brackets
let b: Box[i64] = Box { value: 42 }
```

## Implemented

| Feature | Status |
|---------|--------|
| Generic functions | Complete |
| Generic structs | Complete |
| Generic enums | Complete |
| Nested generics | Complete |
| Tuple return types | Complete |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/types/generics_spec.spl` | BDD spec (12 tests) |

## Dependencies

- Depends on: #10
- Required by: None

## Notes

Uses <T> for declarations and [T] for type arguments. Advanced features (where clauses, const generics) pending.
