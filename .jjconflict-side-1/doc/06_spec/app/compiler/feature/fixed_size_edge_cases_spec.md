# Fixed-Size Array Edge Cases and Boundary Conditions

**Feature ID:** #LANG-008b | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/fixed_size_edge_cases_spec.spl`_

---

## Overview

This spec exercises the boundary conditions and edge cases of fixed-size arrays that go
beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing
on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies
that functional operations like `map`, `filter`, and `reduce` behave correctly when applied
to fixed-size arrays, including cases where `filter` produces a result smaller than the
original size.

## Syntax

```simple
val empty: [i64; 0] = []
val single: [i64; 1] = [42]
val names: [text; 3] = ["alice", "bob", "charlie"]
val flags: [bool; 2] = [true, false]
val big = arr.filter(\x: x > 3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Zero-Size Array | `[T; 0]` is a valid empty fixed-size array that supports iteration |
| Boundary Indexing | Single and two-element arrays test the smallest non-trivial sizes |
| Multi-Type Support | Fixed-size arrays work with `i64`, `f64`, `text`, and `bool` element types |
| Size-Changing Ops | `filter` on a fixed-size array returns a dynamic array that may be smaller |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Fixed-Size Array Edge Cases

#### Size Zero

- ✅ allows size-zero arrays
- ✅ iterates over size-zero arrays
#### Negative Indexing

- ✅ supports negative indices
#### Boundary Conditions

- ✅ handles single element arrays
- ✅ handles two element arrays
#### Mixed Types

- ✅ works with string arrays
- ✅ works with boolean arrays
#### Functional Operations on Fixed

- ✅ map preserves values
- ✅ filter may reduce size
- ✅ reduce works on fixed arrays

