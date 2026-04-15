# Tuple Types Specification

Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of different types without defining a named struct, useful for returning multiple values or temporary groupings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/tuple_types_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/tuple_types/result.json` |

## Scenarios

- creates tuple literal
- gets tuple length
- accesses elements by index
- destructures tuple into variables
- swaps values with tuple destructuring
- destructures from array
- matches tuple pattern
- uses wildcard for unmatched tuples
