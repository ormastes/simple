# Fixed-Size Array Types

> Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry their size as part of the type annotation, enabling stronger guarantees about buffer lengths. This spec validates creation, indexing (including negative indices), read operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional methods (`map`, `filter`, `reduce`) that return dynamic arrays.

<!-- sdn-diagram:id=fixed_size_arrays_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_size_arrays_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_size_arrays_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_size_arrays_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed-Size Array Types

Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry their size as part of the type annotation, enabling stronger guarantees about buffer lengths. This spec validates creation, indexing (including negative indices), read operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional methods (`map`, `filter`, `reduce`) that return dynamic arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/fixed_size_arrays_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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
val doubled = vec3.map(_1 * 2)
val sum = arr.reduce(0, \acc, x: acc + x)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `[T; N]` Syntax | Declares a fixed-size array of type T with exactly N elements |
| Runtime Size Check | Array size is validated at creation to match the declared N |
| Negative Indexing | `arr[-1]` accesses the last element, `arr[-2]` the second-to-last |
| Functional Methods | `map`, `filter`, `reduce` work on fixed arrays but return dynamic arrays |

## Scenarios

### Fixed-Size Arrays

#### Basic Syntax

#### creates fixed-size array with type annotation

1. expect vec3 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3.len() == 3
```

</details>

#### creates fixed-size int array

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

#### creates single element fixed-size array

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 1] = [42]
expect arr[0] == 42
expect arr.len() == 1
```

</details>

#### Indexing

#### allows indexing read

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3[0] == 1.0
expect vec3[1] == 2.0
expect vec3[2] == 3.0
```

</details>

#### allows negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 3] = [10, 20, 30]
expect arr[-1] == 30
expect arr[-2] == 20
expect arr[-3] == 10
```

</details>

#### Read Operations

#### allows len

1. expect vec3 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3.len() == 3
```

</details>

#### allows first and last

1. expect arr first
2. expect arr last


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 4] = [10, 20, 30, 40]
expect arr.first() == 10
expect arr.last() == 40
```

</details>

#### allows contains

1. expect arr contains
2. expect not arr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 3] = [1, 2, 3]
expect arr.contains(2)
expect not arr.contains(5)
```

</details>

#### allows iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [i64; 3] = [1, 2, 3]
var sum = 0
for x in vec3:
    sum = sum + x
expect sum == 6
```

</details>

#### Functional Operations

#### allows map (returns dynamic array)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [i64; 3] = [1, 2, 3]
val doubled = vec3.map(_ * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### allows filter (returns dynamic array)

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 5] = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens[0] == 2
expect evens.len() == 2
```

</details>

#### allows reduce

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 4] = [1, 2, 3, 4]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

#### Display Format

#### displays with size annotation

1. expect vec3 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec3: [i64; 3] = [1, 2, 3]
# FixedSizeArray displays as [items; size]
expect vec3.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
