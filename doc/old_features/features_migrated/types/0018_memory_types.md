# Feature #18: Memory Types

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #18 |
| **Feature Name** | Memory Types |
| **Category** | Types |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Reference capability system with GC-managed references (T), unique pointers (&T), shared pointers (*T), weak pointers (-T), and handle pointers (+T).

## Specification

[doc/spec/memory.md](../../spec/memory.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/hir/types.rs` | Type definitions |

## Pointer Types

| Type | Name | Ownership | Use Case |
|------|------|-----------|----------|
| T | GC Reference | GC-managed | Default, most code |
| &T | Unique Pointer | Single owner | RAII, exclusive access |
| *T | Shared Pointer | Ref-counted | Multiple owners |
| -T | Weak Pointer | Non-owning | Break cycles |
| +T | Handle Pointer | Pool-managed | Entity systems |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/types/memory_types_spec.spl` | BDD spec (15 tests) |

## Dependencies

- Depends on: #10
- Required by: #19

## Notes

GC is default. Manual memory is opt-in via pointer types. RAII for unique pointers. Reference counting for shared pointers.
