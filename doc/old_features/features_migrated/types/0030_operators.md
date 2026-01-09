# Feature #30: Operators

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #30 |
| **Feature Name** | Operators |
| **Category** | Types |
| **Difficulty** | 2 (Easy) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Full set of operators: arithmetic (+, -, *, /, %), comparison (==, !=, <, >, <=, >=), logical (and, or, not), and bitwise operations.

## Specification

[doc/spec/syntax.md](../../doc/spec/syntax.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter.rs` | Implementation |
| `src/parser/src/expressions/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_expressions_tests.rs` | Test suite |

## Dependencies

- Depends on: #1, #2, #10
- Required by: #12, #13

## Notes

Operators follow standard precedence rules. Use parentheses for explicit grouping.
