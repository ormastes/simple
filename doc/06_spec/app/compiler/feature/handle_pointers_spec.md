# Handle Pointers Specification

**Feature ID:** #820-825 | **Category:** Language | **Difficulty:** 3/5 | **Status:** In Progress

_Source: `test/feature/usage/handle_pointers_spec.spl`_

---

## Overview

Handle pointers provide safe, reusable references to objects with automatic lifetime management.
Unlike raw pointers, handles are tracked by the runtime and can be validated, preventing
use-after-free and dangling reference bugs while maintaining performance.

## Syntax

```simple
# Handle type declaration
struct ObjectHandle:
    id: i64
    generation: i32

# Handle creation and usage
val handle = get_handle(obj)
val obj = deref_handle(handle)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Handle | Type-safe reference with runtime validation |
| Generation | Version counter for detecting stale handles |
| Validation | Runtime check that handle points to live object |
| Slot | Handle table entry containing object and metadata |

## Behavior

- Handles are allocated from a handle pool with automatic reuse
- Each handle includes a generation counter to detect stale references
- Deref operation validates handle before returning object reference
- Handle pool manages memory without garbage collection
- Handles can be null/invalid to represent absent values

## Related Specifications

- [References](../references/references_spec.spl) - Reference semantics
- [Memory Management](../memory_management/memory_management_spec.spl) - Lifetime management
- [Error Handling](../error_handling/error_handling_spec.spl) - Invalid handle errors

## Implementation Notes

Handle implementation uses:
- Array-based handle pool with free list
- Generation counters in upper bits
- Index in lower bits for O(1) lookup
- Automatic reuse of freed slots
- Optional inline handle table for small objects

## Examples

```simple
# Create and use handles
val obj = MyObject(data: 42)
val handle = get_handle(obj)
val ref = deref_handle(handle)
expect(ref.data).to_equal(42)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Handle Pointers - Basic

#### with simple handle creation

- ✅ creates handle for object
#### with handle dereferencing

- ✅ dereferences handle safely
### Handle Pointers - Validation

#### with valid handles

- ✅ validates live handle
#### with stale handles

- ✅ detects stale handle
#### with generation counters

- ✅ invalidates handle on object reuse
### Handle Pointers - Pool Management

#### with handle reuse

- ✅ reuses freed slots
#### with multiple handles

- ✅ manages multiple handles
### Handle Pointers - Error Handling

#### with null handle

- ✅ handles null reference
#### with dereferencing errors

- ✅ raises error on invalid deref
### Handle Pointers - Collections

#### with handle arrays

- ✅ stores handles in array
#### with handle dictionaries

- ✅ uses handles as map values

