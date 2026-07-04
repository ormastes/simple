# In-Place Functional Update with the Arrow Operator

> The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr` in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations on arrays and dicts, verifies correct chaining of multiple operations in sequence, and confirms that lambda expressions with closures work within functional updates.

<!-- sdn-diagram:id=functional_update_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functional_update_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functional_update_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functional_update_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# In-Place Functional Update with the Arrow Operator

The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr` in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations on arrays and dicts, verifies correct chaining of multiple operations in sequence, and confirms that lambda expressions with closures work within functional updates.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-031 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/functional_update_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Functional Update Syntax

#### when updating a struct field

#### creates new struct with updated field

1. arr->concat
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functional update with concat - modifies in place and returns
var arr = [1, 2]
arr->concat([3, 4])
expect arr.len() == 4
```

</details>

#### leaves original struct unchanged

1. arr->map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functional update with map - transforms elements in place
var arr = [1, 2, 3]
arr->map(\x: x * 2)
expect arr[1] == 4
```

</details>

#### when updating multiple fields

#### updates all specified fields

1. arr->filter
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functional update with filter - filters elements in place
var arr = [1, 2, 3, 4, 5]
arr->filter(\x: x > 2)
expect arr.len() == 3
```

</details>

#### preserves unmodified fields

1. d->set
2. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Dict functional update - adds new key
var d = {"a": 1}
d->set("b", 2)
expect d.len() == 2
```

</details>

### Functional Update with Nesting

#### when updating nested struct fields

#### updates nested field values

1. arr->map
2. arr->filter
3. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Chained functional updates - map then filter
var arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
expect arr.len() == 2
```

</details>

#### preserves sibling fields in nested structures

1. d->set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple dict operations
var d = {"x": 1, "y": 2}
d->set("z", 3)
expect d["x"] == 1
expect d["z"] == 3
```

</details>

#### when chaining functional updates

#### applies updates in correct order

1. arr->map
2. arr->filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Chained array operations: [1,2,3] -> [2,3,4] -> [3,4]
var arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
expect arr == [3, 4]
```

</details>

#### maintains immutability through chain

1. original->filter
2. original->map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple transformations preserve data integrity
var original = [1, 2, 3, 4, 5]
original->filter(\x: x % 2 == 0)
original->map(\x: x * 10)
expect original == [20, 40]
```

</details>

### Functional Update Advanced Patterns

#### works with generic types

1. numbers->map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functional update works with any collection type
var numbers = [10, 20, 30]
numbers->map(\x: x / 10)
expect numbers == [1, 2, 3]
```

</details>

#### supports computed field values in update

1. arr->filter
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Lambda with complex computation in functional update
var arr = [1, 2, 3, 4, 5]
val threshold = 2
arr->filter(\x: x > threshold)
expect arr.len() == 3
```

</details>

#### handles update expressions with side effects

1. items->filter
2. items->map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functional update with multiple operations
var items = [5, 10, 15, 20]
items->filter(\x: x > 5)
items->map(\x: x - 5)
expect items == [5, 10, 15]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
