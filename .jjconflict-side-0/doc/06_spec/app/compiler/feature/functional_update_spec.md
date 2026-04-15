# In-Place Functional Update with the Arrow Operator

**Feature ID:** #LANG-031 | **Category:** Language | **Status:** Active

_Source: `test/feature/usage/functional_update_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Functional Update Syntax

#### when updating a struct field

- ✅ creates new struct with updated field
- ✅ leaves original struct unchanged
#### when updating multiple fields

- ✅ updates all specified fields
- ✅ preserves unmodified fields
### Functional Update with Nesting

#### when updating nested struct fields

- ✅ updates nested field values
- ✅ preserves sibling fields in nested structures
#### when chaining functional updates

- ✅ applies updates in correct order
- ✅ maintains immutability through chain
### Functional Update Advanced Patterns

- ✅ works with generic types
- ✅ supports computed field values in update
- ✅ handles update expressions with side effects

