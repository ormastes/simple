# Collections Specification

Tests for collection types including arrays, tuples, dictionaries, and strings. Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLLECTIONS-001 |
| Category | Language \| Collections |
| Status | Implemented |
| Source | `test/feature/usage/collections_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for collection types including arrays, tuples, dictionaries, and strings.
Covers basic operations, functional methods, comprehensions, slicing, and spread operators.

## Syntax

```simple
var arr = [1, 2, 3]                    # Array literal
val t = (10, 20, 30)                   # Tuple literal
val d = {"a": 1, "b": 2}               # Dictionary literal
val doubled = arr.map(\x: x * 2)       # Functional method
val squares = [x * x for x in arr]    # List comprehension
val sub = arr[1:4]                     # Slicing
val last = arr[-1]                     # Negative indexing
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/collections/result.json` |

## Scenarios

- creates array literal and accesses by index
- gets array length
- gets first and last elements
- checks if array contains element
- checks if array is empty
- creates tuple literal and accesses by index
- gets tuple length
- destructures tuple
- creates dict literal and accesses by key
- gets dict length
- checks if dict contains key
- gets value from dict
- gets string length
- checks if string contains substring
- indexes string to get character
- pushes element to array
- concatenates two arrays
- slices array
- maps array elements
- filters array elements
- reduces array to single value
- checks all elements match predicate
- joins array elements to string
- sums array elements
- reverses array
- sets new key in dict
- removes key from dict
- merges two dicts
- gets with default value
- creates list with basic comprehension
- creates list with condition
- creates squares list
- creates dict with comprehension
- slices with start and end
- slices from start index to end
- slices from beginning to end index
- slices with step
- accesses last element with -1
- accesses second from end with -2
- accesses string with negative index
- spreads two arrays
- spreads with mixed elements
- unpacks basic tuple
- unpacks with swap pattern
- unpacks array to tuple
- evaluates basic chained comparison
- evaluates false chained comparison
- evaluates three-way comparison
- evaluates mixed comparison operators
- executes basic with block
- binds resource with as
- calls __enter__ and __exit__ on class
- applies basic decorator
- applies decorator with arguments
