# Feature #21: Dicts

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #21 |
| **Feature Name** | Dicts |
| **Category** | Data Structures |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Dictionary (hash map) type with string keys. Supports literal syntax, key access, iteration, and methods like keys, values, contains_key.

## Specification

[doc/spec/data_structures.md](../../doc/spec/data_structures.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/runtime/src/value/collections.rs` | Implementation |
| `src/compiler/src/interpreter.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_collections_tests.rs` | Test suite |

## Dependencies

- Depends on: #1, #2, #10, #25
- Required by: #11

## Notes

Dict uses {} literal syntax. Keys are strings by default.
