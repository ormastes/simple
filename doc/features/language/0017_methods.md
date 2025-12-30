# Feature #17: Methods

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #17 |
| **Feature Name** | Methods |
| **Category** | Language |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Instance methods with self parameter, static methods, and method chaining. Methods are defined inside class bodies.

## Specification

[doc/spec/data_structures.md](../../doc/spec/data_structures.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter_method.rs` | Implementation |
| `src/parser/src/statements/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_oop_tests.rs` | Test suite |

## Dependencies

- Depends on: #1, #2, #11, #12
- Required by: #20, #21

## Notes

Methods use self for instance access. Static methods have no self parameter.
