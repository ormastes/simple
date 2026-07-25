# Fixed-Size Array Edge Cases and Boundary Conditions

> This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies that functional operations like `map`, `filter`, and `reduce` behave correctly when applied to fixed-size arrays, including cases where `filter` produces a result smaller than the original size.

<!-- sdn-diagram:id=fixed_size_edge_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_size_edge_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_size_edge_cases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_size_edge_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed-Size Array Edge Cases and Boundary Conditions

This spec exercises the boundary conditions and edge cases of fixed-size arrays that go beyond typical usage. It tests zero-length arrays, single-element arrays, negative indexing on various sizes, and fixed-size arrays of non-numeric types (text, bool). It also verifies that functional operations like `map`, `filter`, and `reduce` behave correctly when applied to fixed-size arrays, including cases where `filter` produces a result smaller than the original size.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008b |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/fixed_size_edge_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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
val big = arr.filter(_1 > 3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Zero-Size Array | `[T; 0]` is a valid empty fixed-size array that supports iteration |
| Boundary Indexing | Single and two-element arrays test the smallest non-trivial sizes |
| Multi-Type Support | Fixed-size arrays work with `i64`, `f64`, `text`, and `bool` element types |
| Size-Changing Ops | `filter` on a fixed-size array returns a dynamic array that may be smaller |

## Scenarios

### Fixed-Size Array Edge Cases

#### Size Zero

#### allows size-zero arrays

1. expect empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64; 0] = []
expect empty.len() == 0
```

</details>

#### iterates over size-zero arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64; 0] = []
var count = 0
for _ in empty:
    count = count + 1
expect count == 0
```

</details>

#### Negative Indexing

#### supports negative indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr[-1] == 5
expect arr[-2] == 4
expect arr[-3] == 3
```

</details>

#### Boundary Conditions

#### handles single element arrays

1. expect single len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single: [i64; 1] = [42]
expect single[0] == 42
expect single.len() == 1
```

</details>

#### handles two element arrays

1. expect pair len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair: [i64; 2] = [10, 20]
expect pair[0] == 10
expect pair[1] == 20
expect pair.len() == 2
```

</details>

#### Mixed Types

#### works with string arrays

1. expect names len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names: [text; 3] = ["alice", "bob", "charlie"]
expect names[0] == "alice"
expect names.len() == 3
```

</details>

#### works with boolean arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags: [bool; 2] = [true, false]
expect flags[0] == true
expect flags[1] == false
```

</details>

#### Functional Operations on Fixed

#### map preserves values

1. expect doubled len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 4] = [1, 2, 3, 4]
val doubled = arr.map(_1 * 2)
expect doubled[0] == 2
expect doubled.len() == 4
expect doubled[3] == 8
```

</details>

#### filter may reduce size

1. expect big len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 5] = [1, 2, 3, 4, 5]
val big = arr.filter(_1 > 3)
expect big[0] == 4
expect big.len() == 2
expect big[1] == 5
```

</details>

#### reduce works on fixed arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64; 3] = [10, 20, 30]
val total = arr.reduce(0, \acc, x: acc + x)
expect total == 60
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
