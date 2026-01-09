# Feature #6: RuntimeValue

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #6 |
| **Feature Name** | RuntimeValue |
| **Category** | Infrastructure |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Tagged pointer value system with 64-bit encoding. Supports integers (61-bit), floats, booleans, nil, strings, arrays, dicts, and heap objects with type tagging.

## Specification

[doc/architecture/README.md](../../architecture/README.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/runtime/src/value/core.rs` | Core RuntimeValue type |
| `src/runtime/src/value/tags.rs` | Tag constants |
| `src/runtime/src/value/heap.rs` | Heap object headers |

## Value Tags

| Tag | Type | Encoding |
|-----|------|----------|
| TAG_INT | Integer | 61-bit signed |
| TAG_FLOAT | Float | IEEE 754 NaN-boxed |
| TAG_SPECIAL | Bool/Nil | Special constants |
| TAG_HEAP | Objects | Pointer to heap |

## Heap Types

| Type | Description |
|------|-------------|
| RuntimeString | UTF-8 string |
| RuntimeArray | Dynamic array |
| RuntimeDict | Hash map |
| RuntimeTuple | Fixed-size tuple |
| RuntimeObject | Struct instance |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/infrastructure/runtime_value_spec.spl` | BDD spec (20 tests) |

## Dependencies

- Depends on: None (foundational component)
- Required by: #7, #100

## Notes

Uses NaN-boxing for floats. Heap objects share common header. FFI bridge for compiled code interop.
