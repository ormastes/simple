# Feature #19: Borrowing

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #19 |
| **Feature Name** | Borrowing |
| **Category** | Types |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Ownership semantics with move, borrow, and lifetime tracking. Ensures memory safety without garbage collection for manual memory types.

## Specification

[doc/spec/memory.md](../../spec/memory.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/hir/types.rs` | Borrow checking |

## Ownership Rules

| Rule | Description |
|------|-------------|
| Single Owner | Each value has exactly one owner |
| Move | Assignment transfers ownership |
| Drop | Value dropped when owner goes out of scope |
| Borrow | Temporary reference without ownership |

## Borrow Rules

| Type | Count | Mutation |
|------|-------|----------|
| Immutable | Multiple | No |
| Mutable | One | Yes |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/types/borrowing_spec.spl` | BDD spec (15 tests) |

## Dependencies

- Depends on: #18
- Required by: None

## Notes

Move transfers ownership. Borrow creates temporary reference. Lifetimes prevent dangling pointers. Checked at compile time.
