# Fixed-Size Array Types

**Feature ID:** #LANG-008 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/fixed_size_arrays_spec.spl`_

---

## Overview

Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at
declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry
their size as part of the type annotation, enabling stronger guarantees about buffer
lengths. This spec validates creation, indexing (including negative indices), read
operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional
methods (`map`, `filter`, `reduce`) that return dynamic arrays.

## Syntax

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr[-1] == 5
val doubled = vec3.map(\x: x * 2)
val sum = arr.reduce(0, \acc, x: acc + x)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `[T; N]` Syntax | Declares a fixed-size array of type T with exactly N elements |
| Runtime Size Check | Array size is validated at creation to match the declared N |
| Negative Indexing | `arr[-1]` accesses the last element, `arr[-2]` the second-to-last |
| Functional Methods | `map`, `filter`, `reduce` work on fixed arrays but return dynamic arrays |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### Fixed-Size Arrays

#### Basic Syntax

- ✅ creates fixed-size array with type annotation
- ✅ creates fixed-size int array
- ✅ creates single element fixed-size array
#### Indexing

- ✅ allows indexing read
- ✅ allows negative indexing
#### Read Operations

- ✅ allows len
- ✅ allows first and last
- ✅ allows contains
- ✅ allows iteration
#### Functional Operations

- ✅ allows map (returns dynamic array)
- ✅ allows filter (returns dynamic array)
- ✅ allows reduce
#### Display Format

- ✅ displays with size annotation

