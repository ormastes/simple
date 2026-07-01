# Collections (Python-Inspired Sample)

> Tests compilation of collection types inspired by Python including lists, maps, and iteration patterns. Verifies that collection literals, comprehensions, and standard collection operations compile correctly through the native pipeline.

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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections (Python-Inspired Sample)

Tests compilation of collection types inspired by Python including lists, maps, and iteration patterns. Verifies that collection literals, comprehensions, and standard collection operations compile correctly through the native pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/collections_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of collection types inspired by Python including lists, maps,
and iteration patterns. Verifies that collection literals, comprehensions, and
standard collection operations compile correctly through the native pipeline.

## Scenarios

### Collections

#### list operations

#### creates list literal

1. expect numbers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
expect numbers.len() == 5
```

</details>

#### accesses elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [10, 20, 30]
expect items[0] == 10
expect items[2] == 30
```

</details>

#### iterates over list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3]
var sum = 0
for n in numbers:
    sum = sum + n
expect sum == 6
```

</details>

#### dict operations

#### creates dict literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val person = {"name": "Alice", "age": 30}
expect person["name"] == "Alice"
```

</details>

#### adds and retrieves values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = {}
m["key"] = "value"
expect m["key"] == "value"
```

</details>

#### checks key existence

1. expect m has
2. expect not m has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {"a": 1}
expect m.has("a")
expect not m.has("b")
```

</details>

#### list comprehensions

#### creates list with comprehension

1. expect squares len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [for x in [1, 2, 3, 4]: x * x]
expect squares[0] == 1
expect squares.len() == 4
expect squares[3] == 16
```

</details>

#### filters with comprehension

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evens = [for x in [1, 2, 3, 4, 5, 6] if x % 2 == 0: x]
expect evens.len() == 3
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
