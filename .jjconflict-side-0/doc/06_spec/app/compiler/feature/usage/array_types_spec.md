# Array Type System and Operations

Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, slicing with `start:end:step` notation, and a full suite of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive spec covers eight aspects of array behavior: basic creation and queries, mutation via `push` and `concat`, functional transformations, Python-style slicing, negative indexing, the spread operator (`*`) for array merging, list comprehensions with optional filter clauses, and chained comparison expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-003 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/array_types_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Arrays are Simple's primary ordered collection type, supporting literal construction,
positive and negative indexing, slicing with `start:end:step` notation, and a full suite
of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive
spec covers eight aspects of array behavior: basic creation and queries, mutation via `push`
and `concat`, functional transformations, Python-style slicing, negative indexing, the
spread operator (`*`) for array merging, list comprehensions with optional filter clauses,
and chained comparison expressions.

## Syntax

```simple
var arr = [1, 2, 3, 4, 5]
val doubled = arr.map(\x: x * 2)
val sub = arr[1:4]
val evens = [x for x in arr if x % 2 == 0]
val merged = [*a, *b]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Array Literal | `[1, 2, 3]` creates a dynamic array with inferred element type |
| Slicing | `arr[start:end:step]` extracts sub-arrays using Python-style notation |
| Spread Operator | `[*a, *b]` unpacks arrays inline to build a new merged array |
| List Comprehension | `[expr for x in iter if cond]` builds arrays with inline loops and filters |
| Functional Methods | `map`, `filter`, `reduce`, `all`, `join`, `sum` for declarative transforms |
| Negative Indexing | `arr[-1]` accesses elements from the end of the array |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/array_types/result.json` |

## Scenarios

- creates array from literal
- gets array length
- gets first and last elements
- checks if array contains element
- checks if array is empty
- checks non-empty array
- pushes element to array
- concatenates two arrays
- reverses array
- maps function over array
- filters array by predicate
- reduces array with accumulator
- checks all elements match predicate
- joins array elements with separator
- sums numeric array
- slices with start and end
- slices from start index to end
- slices from beginning to end index
- slices with step
- gets last element with -1
- gets second from end with -2
- spreads arrays with *
- spreads array mixed with elements
- creates list from comprehension
- filters with comprehension condition
- creates squares with comprehension
- evaluates basic chained comparison
- evaluates false chained comparison
- evaluates three-way comparison
- evaluates mixed comparison operators
