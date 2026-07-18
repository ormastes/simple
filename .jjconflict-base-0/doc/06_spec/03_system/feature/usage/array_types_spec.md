# Array Type System and Operations

> Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, slicing with `start:end:step` notation, and a full suite of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive spec covers eight aspects of array behavior: basic creation and queries, mutation via `push` and `concat`, functional transformations, Python-style slicing, negative indexing, the spread operator (`*`) for array merging, list comprehensions with optional filter clauses, and chained comparison expressions.

<!-- sdn-diagram:id=array_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=array_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

array_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=array_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Type System and Operations

Arrays are Simple's primary ordered collection type, supporting literal construction, positive and negative indexing, slicing with `start:end:step` notation, and a full suite of functional methods (`map`, `filter`, `reduce`, `all`, `join`, `sum`). This comprehensive spec covers eight aspects of array behavior: basic creation and queries, mutation via `push` and `concat`, functional transformations, Python-style slicing, negative indexing, the spread operator (`*`) for array merging, list comprehensions with optional filter clauses, and chained comparison expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-003 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/array_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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
val doubled = arr.map(_1 * 2)
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

## Scenarios

### Array Basics

#### array literals

#### creates array from literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr[2] == 3
```

</details>

#### gets array length

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
expect arr.len() == 3
```

</details>

#### gets first and last elements

1. expect arr first


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [5, 10, 15, 20]
expect arr.first() + arr.last() == 25
```

</details>

#### array queries

#### checks if array contains element

1. expect arr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
expect arr.contains(2)
```

</details>

#### checks if array is empty

1. expect arr is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
expect arr.is_empty()
```

</details>

#### checks non-empty array

1. expect not arr is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1]
expect not arr.is_empty()
```

</details>

### Array Modification

#### push and concat

#### pushes element to array

1. arr = arr push


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr[3] == 4
```

</details>

#### concatenates two arrays

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2]
val b = [3, 4]
val c = a.concat(b)
expect c.len() == 4
```

</details>

#### reverse

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val rev = arr.reverse()
expect rev[0] == 3
```

</details>

### Array Functional Methods

#### map

#### maps function over array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val doubled = arr.map(_ * 2)
expect doubled[1] == 4
```

</details>

#### filter

#### filters array by predicate

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens.len() == 2
```

</details>

#### reduce

#### reduces array with accumulator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 15
```

</details>

#### all and any

#### checks all elements match predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [2, 4, 6]
val all_even = arr.all(_1 % 2 == 0)
expect all_even
```

</details>

#### join

#### joins array elements with separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val s = arr.join("-")
expect s == "1-2-3"
```

</details>

#### sum

#### sums numeric array

1. expect arr sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr.sum() == 15
```

</details>

### Array Slicing

#### basic slicing

#### slices with start and end

1. expect sub len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4, 5]
val sub = arr[1:4]
expect sub.len() == 3
```

</details>

#### slices from start index to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4]
val sub = arr[2:]
expect sub[0] == 2
```

</details>

#### slices from beginning to end index

1. expect sub len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4]
val sub = arr[:3]
expect sub.len() == 3
```

</details>

#### step slicing

#### slices with step

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0, 1, 2, 3, 4, 5, 6, 7]
val evens = arr[::2]
expect evens.len() == 4
```

</details>

### Negative Indexing

#### gets last element with -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30, 40, 50]
expect arr[-1] == 50
```

</details>

#### gets second from end with -2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr[-2] == 4
```

</details>

### Array Spread Operator

#### spreads arrays with *

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [4, 5]
val c = [*a, *b]
expect c.len() == 5
```

</details>

#### spreads array mixed with elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [2, 3]
var arr = [1, *a, 4]
expect arr[2] == 3
```

</details>

### List Comprehension

#### creates list from comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
val doubled = [x * 2 for x in arr]
expect doubled[2] == 6
```

</details>

#### filters with comprehension condition

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5, 6]
val evens = [x for x in arr if x % 2 == 0]
expect evens.len() == 3
```

</details>

#### creates squares with comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [x * x for x in [1, 2, 3, 4]]
expect squares[3] == 16
```

</details>

### Chained Comparisons

#### evaluates basic chained comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
expect 0 < x and x < 10
```

</details>

#### evaluates false chained comparison

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 15
expect not (0 < x and x < 10)
```

</details>

#### evaluates three-way comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 5
val c = 10
expect a < b and b < c
```

</details>

#### evaluates mixed comparison operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
expect 0 <= x and x <= 10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
