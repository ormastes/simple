# Feature #11: Classes

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #11 |
| **Feature Name** | Classes |
| **Category** | Language |
| **Difficulty** | 4 (Hard) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Object-oriented programming with class definitions, typed fields, methods, static methods, and struct-literal instantiation. Supports single inheritance.

## Specification

[doc/spec/data_structures.md](../../doc/spec/data_structures.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter.rs` | Implementation |
| `src/compiler/src/interpreter_method.rs` | Implementation |
| `src/parser/src/statements/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_oop_tests.rs` | Test suite |

## Examples

```simple
# Define a class with fields and methods
# class Point: x: Int, y: Int
# let p = Point { x: 3, y: 4 }
# print(p.x)  # 3
```

## Dependencies

- Depends on: #1, #2, #12

## Notes

Classes support struct-literal syntax for instantiation. Methods use self parameter for instance access.
