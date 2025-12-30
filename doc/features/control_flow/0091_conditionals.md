# Feature #91: Conditionals

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #91 |
| **Feature Name** | Conditionals |
| **Category** | Control Flow |
| **Difficulty** | 2 (Easy) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Conditional statements with if, elif, and else branches. Supports boolean expressions and logical operators.

## Specification

[doc/spec/syntax.md](../../doc/spec/syntax.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/interpreter_control.rs` | Implementation |
| `src/parser/src/statements/mod.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_control.rs` | Test suite |

## Dependencies

- Depends on: #1, #2, #10
- Required by: #13, #90

## Notes

Uses Python-style indentation. Supports and, or, not operators.
