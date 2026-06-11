# Collections (Interpreter)

> Tests collection type handling in the interpreter including lists, maps, and iteration. Verifies that collection operations produce correct results when executed in interpreted mode with proper element access and mutation.

<!-- sdn-diagram:id=collections_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collections_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collections_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collections_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections (Interpreter)

Tests collection type handling in the interpreter including lists, maps, and iteration. Verifies that collection operations produce correct results when executed in interpreted mode with proper element access and mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/collections_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests collection type handling in the interpreter including lists, maps, and
iteration. Verifies that collection operations produce correct results when
executed in interpreted mode with proper element access and mutation.

## Scenarios

### Collections

#### list operations

#### creates list literal

1. expect items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
expect items.len() == 3
```

</details>

#### accesses by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["a", "b", "c"]
expect items[0] == "a"
expect items[2] == "c"
```

</details>

#### supports negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [10, 20, 30]
expect items[-1] == 30
```

</details>

#### slices list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
expect items[1:4] == [2, 3, 4]
```

</details>

#### dictionary operations

#### creates dict literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"alice": 30, "bob": 25}
expect ages["alice"] == 30
```

</details>

#### checks key existence

1. expect data has
2. expect data has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"key": "value"}
expect data.has("key") == true
expect data.has("missing") == false
```

</details>

#### collection methods

#### maps over list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
val doubled = nums.map(_ * 2)
expect doubled == [2, 4, 6]
```

</details>

#### filters list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
val evens = nums.filter(_ % 2 == 0)
expect evens == [2, 4]
```

</details>

#### list comprehensions

#### creates list with comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [for x in 0..5: x * x]
expect squares == [0, 1, 4, 9, 16]
```

</details>

#### filters in comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evens = [for x in 0..10 if x % 2 == 0: x]
expect evens == [0, 2, 4, 6, 8]
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
