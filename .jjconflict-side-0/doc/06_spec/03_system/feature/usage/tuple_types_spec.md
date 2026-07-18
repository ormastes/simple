# Tuple Types Specification

> Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of different types without defining a named struct, useful for returning multiple values or temporary groupings.

<!-- sdn-diagram:id=tuple_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tuple_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tuple_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tuple_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tuple Types Specification

Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of different types without defining a named struct, useful for returning multiple values or temporary groupings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/tuple_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Tuple Types

#### tuple creation

#### creates tuple literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 30)
expect t[1] == 20
```

</details>

#### gets tuple length

1. expect t len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2, 3, 4)
expect t.len() == 4
```

</details>

#### tuple access

#### accesses elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (5, 10, 15)
expect t[0] == 5
expect t[2] == 15
```

</details>

#### tuple destructuring

#### destructures tuple into variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (a, b, c) = (10, 20, 30)
expect a + b + c == 60
```

</details>

#### swaps values with tuple destructuring

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val (x, y) = (b, a)
expect x == 20
```

</details>

#### destructures from array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [5, 10, 15]
val (first, second, third) = arr
expect second == 10
```

</details>

### Tuple Pattern Matching

#### matches tuple pattern

1.


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2)
val result = match t:
    (1, x) => x * 10
    _ => 0
expect result == 20
```

</details>

#### uses wildcard for unmatched tuples

1.


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (5, 5)
val result = match t:
    (1, x) => x
    _ => 99
expect result == 99
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
