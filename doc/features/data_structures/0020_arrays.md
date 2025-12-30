# Feature #20: Arrays

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #20 |
| **Feature Name** | Arrays |
| **Category** | Data Structures |
| **Difficulty** | 2 (Easy) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Dynamic arrays (lists) with built-in methods: len, push, pop, map, filter, reduce, find, contains, sort, reverse, slice, and more.

## Specification

[doc/spec/data_structures.md](../../doc/spec/data_structures.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/runtime/src/value/collections.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/interpreter_collections_tests.rs` | Test suite |

## Examples

```simple
let nums = [1, 2, 3, 4, 5]

# Basic operations
let length = nums.len()        # 5
let first = nums[0]            # 1

# Higher-order methods
let doubled = nums.map(\x: x * 2)
let evens = nums.filter(\x: x % 2 == 0)
let sum = nums.reduce(0, \a, b: a + b)
```

## Dependencies

- Depends on: #1, #2
- Required by: #11, #12

## Notes

Arrays are dynamically sized. Use concatenation (+) for adding elements.
