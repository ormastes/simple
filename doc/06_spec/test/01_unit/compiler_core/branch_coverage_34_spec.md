# Branch Coverage Test Suite - Struct Arrays & Nested Types

> Tests struct arrays and nested type structures to cover emit_array_literal_pushes (lines 1901, 1911) and array_elem_stype (line 416).

<!-- sdn-diagram:id=branch_coverage_34_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_34_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_34_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_34_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Struct Arrays & Nested Types

Tests struct arrays and nested type structures to cover emit_array_literal_pushes (lines 1901, 1911) and array_elem_stype (line 416).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #STRUCT_ARRAY #NESTED_TYPES |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_34_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests struct arrays and nested type structures to cover
emit_array_literal_pushes (lines 1901, 1911) and array_elem_stype (line 416).

## Scenarios

### Struct Arrays

#### array of simple structs

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val points = [Point(x: 1, y: 2), Point(x: 3, y: 4)]
check(points.len() == 2)
check(points[0].x == 1)
check(points[1].y == 4)
```

</details>

#### array of structs with multiple fields

1. Data
2. Data
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Data:
    id: i64
    value: i64
    active: bool

val items = [
    Data(id: 1, value: 100, active: true),
    Data(id: 2, value: 200, active: false)
]
check(items.len() == 2)
check(items[0].active)
check(not items[1].active)
```

</details>

#### empty struct array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Empty:
    pass

val arr: [Empty] = []
check(arr.len() == 0)
```

</details>

### Nested Arrays

#### 2d integer array

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr2d: [[i64]] = [[1, 2], [3, 4], [5, 6]]
check(arr2d.len() == 3)
check(arr2d[0].len() == 2)
check(arr2d[0][0] == 1)
check(arr2d[2][1] == 6)
```

</details>

#### 3d array

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr3d: [[[i64]]] = [[[1, 2]], [[3, 4]]]
check(arr3d.len() == 2)
check(arr3d[0][0][0] == 1)
```

</details>

#### jagged arrays

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jagged = [[1], [2, 3], [4, 5, 6]]
check(jagged[0].len() == 1)
check(jagged[1].len() == 2)
check(jagged[2].len() == 3)
```

</details>

#### nested array of strings

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strs: [[text]] = [["a", "b"], ["c", "d"]]
check(strs[0][0] == "a")
check(strs[1][1] == "d")
```

</details>

### Arrays of Optional Types

#### optional integer array

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts: [i64?] = [Some(1), nil, Some(3)]
check(opts.len() == 3)
check(opts[0].?)
check(not opts[1].?)
check(opts[2].?)
```

</details>

#### optional struct array

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Value:
    n: i64

val items: [Value?] = [Some(Value(n: 1)), nil]
check(items[0].?)
check(not items[1].?)
```

</details>

### Complex Nested Structures

#### array of arrays of optionals

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val complex: [[i64?]] = [[Some(1), nil], [Some(2), Some(3)]]
check(complex[0][0].?)
check(not complex[0][1].?)
```

</details>

#### struct containing arrays

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Container:
    values: [i64]

val c = Container(values: [1, 2, 3])
check(c.values.len() == 3)
```

</details>

#### nested struct array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Inner:
    x: i64

struct Outer:
    inner: Inner

val items = [Outer(inner: Inner(x: 1)), Outer(inner: Inner(x: 2))]
check(items[0].inner.x == 1)
```

</details>

### Array Element Type Extraction

#### simple type arrays

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ints: [i64] = [1, 2, 3]
val floats: [f64] = [1.0, 2.0]
val bools: [bool] = [true, false]
check(ints.len() > 0)
check(floats.len() > 0)
check(bools.len() > 0)
```

</details>

#### text arrays

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val texts: [text] = ["a", "b", "c"]
check(texts[0] == "a")
```

</details>

### Array Literal Initialization

#### mixed expressions in array

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val arr = [x, x + 1, x + 2, x * 2]
check(arr[0] == 5)
check(arr[1] == 6)
check(arr[3] == 10)
```

</details>

#### nested literals

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [
    [1, 2, 3],
    [4, 5, 6],
    [7, 8, 9]
]
check(nested[1][1] == 5)
```

</details>

#### deep nesting

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep = [
    [[1, 2], [3, 4]],
    [[5, 6], [7, 8]]
]
check(deep[0][0][0] == 1)
check(deep[1][1][1] == 8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
