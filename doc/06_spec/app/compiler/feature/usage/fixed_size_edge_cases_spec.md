# Fixed-Size Array Edge Cases and Boundary Conditions

This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies that functional operations like `map`, `filter`, and `reduce` behave correctly when applied to fixed-size arrays, including cases where `filter` produces a result smaller than the original size.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008b |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/fixed_size_edge_cases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/fixed_size_edge_cases/result.json` |

## Scenarios

- allows size-zero arrays
- iterates over size-zero arrays
- supports negative indices
- handles single element arrays
- handles two element arrays
- works with string arrays
- works with boolean arrays
- map preserves values
- filter may reduce size
- reduce works on fixed arrays
