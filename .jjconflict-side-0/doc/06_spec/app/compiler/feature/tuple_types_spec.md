# Tuple Types Specification

**Feature ID:** #TBD | **Category:** Language | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/tuple_types_spec.spl`_

---

## Overview

Tuple types are ordered collections of heterogeneous values with fixed length.
They allow grouping multiple values of different types without defining a
named struct, useful for returning multiple values or temporary groupings.

## Syntax

```simple
val point = (3, 4)
val mixed = ("hello", 42, true)
val (x, y) = point  # Destructuring
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tuple | Fixed-size heterogeneous collection |
| Tuple Type | Type annotation like `(T1, T2, T3)` |
| Destructuring | Pattern matching to extract tuple elements |
| Unit Type | Empty tuple `()` representing no value |

## Behavior

- Tuples have fixed length determined at compile time
- Elements accessed by index: `tuple[0]`, `tuple[1]`
- Support pattern matching and destructuring
- Unit type `()` is the zero-element tuple

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Tuple Types

#### tuple creation

- ✅ creates tuple literal
- ✅ gets tuple length
#### tuple access

- ✅ accesses elements by index
#### tuple destructuring

- ✅ destructures tuple into variables
- ✅ swaps values with tuple destructuring
- ✅ destructures from array
### Tuple Pattern Matching

- ✅ matches tuple pattern
- ✅ uses wildcard for unmatched tuples

