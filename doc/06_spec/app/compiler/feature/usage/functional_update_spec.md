# In-Place Functional Update with the Arrow Operator

The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr` in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations on arrays and dicts, verifies correct chaining of multiple operations in sequence, and confirms that lambda expressions with closures work within functional updates.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-031 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/functional_update_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The functional update operator `->` applies transformations to collections in place,
enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow
operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr`
in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations
on arrays and dicts, verifies correct chaining of multiple operations in sequence,
and confirms that lambda expressions with closures work within functional updates.

## Syntax

```simple
var arr = [1, 2, 3]
arr->map(\x: x + 1)               # arr is now [2, 3, 4]
arr->filter(\x: x > 2)            # arr is now [3, 4]

var d = {"a": 1}
d->set("b", 2)                    # d now has keys "a" and "b"

var items = [5, 10, 15, 20]
items->filter(\x: x > 5)          # chained in-place transforms
items->map(\x: x - 5)             # items is now [5, 10, 15]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `->` operator | Applies a transformation to a collection in place, mutating the variable |
| `->map` | Transforms each element using a lambda, updating the collection in place |
| `->filter` | Retains only elements matching a predicate, modifying the collection in place |
| `->concat` | Appends another collection's elements to the target in place |
| `->set` | Adds or updates a key-value pair in a dict in place |
| Chained updates | Multiple `->` operations can be applied sequentially for data pipelines |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/functional_update/result.json` |

## Scenarios

- creates new struct with updated field
- leaves original struct unchanged
- updates all specified fields
- preserves unmodified fields
- updates nested field values
- preserves sibling fields in nested structures
- applies updates in correct order
- maintains immutability through chain
- works with generic types
- supports computed field values in update
- handles update expressions with side effects
