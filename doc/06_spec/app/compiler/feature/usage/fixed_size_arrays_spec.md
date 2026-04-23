# Fixed-Size Array Types

Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry their size as part of the type annotation, enabling stronger guarantees about buffer lengths. This spec validates creation, indexing (including negative indices), read operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional methods (`map`, `filter`, `reduce`) that return dynamic arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/fixed_size_arrays_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/fixed_size_arrays/result.json` |

## Scenarios

- creates fixed-size array with type annotation
- creates fixed-size int array
- creates single element fixed-size array
- allows indexing read
- allows negative indexing
- allows len
- allows first and last
- allows contains
- allows iteration
- allows map (returns dynamic array)
- allows filter (returns dynamic array)
- allows reduce
- displays with size annotation
