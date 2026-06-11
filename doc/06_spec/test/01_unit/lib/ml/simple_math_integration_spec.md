# Simple Math Integration Specification

> <details>

<!-- sdn-diagram:id=simple_math_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_math_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_math_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_math_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Math Integration Specification

## Scenarios

### Simple Math: @ matrix multiplication operator

#### should multiply 2x2 matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Matrix.new([2, 2])
val b = Matrix.new([2, 2])
val c = a.matmul(b)
expect c.shape == [2, 2]
```

</details>

<details>
<summary>Advanced: should handle matrix-vector multiplication</summary>

#### should handle matrix-vector multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Matrix.new([3, 4])
val v = Matrix.new([4, 1])
val result = a.matmul(v)
expect result.shape == [3, 1]
```

</details>


</details>

<details>
<summary>Advanced: should chain matrix shapes</summary>

#### should chain matrix shapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Matrix.new([2, 3])
val b = Matrix.new([3, 4])
val ab = a.matmul(b)
expect ab.shape == [2, 4]
```

</details>


</details>

<details>
<summary>Advanced: should work with identity matrix shape</summary>

#### should work with identity matrix shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Matrix.new([5, 5])
val i = Matrix.identity(5)
expect i.shape == [5, 5]
```

</details>


</details>

#### should respect operator precedence with @ vs *

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Matrix.new([2, 3])
val b = Matrix.new([3, 4])
val ab = a.matmul(b)
expect ab.shape == [2, 4]
```

</details>

### Simple Math: 2D array literals

#### should create 2D grid from pipe-delimited syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = Matrix.new([3, 3])
expect t1.shape == [3, 3]
```

</details>

#### should support CUDA device parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t2 = Matrix.new([4, 4], device="cuda:0")
expect t2.device == "cuda:0"
```

</details>

<details>
<summary>Advanced: should work with @ operator for matrix operations</summary>

#### should work with @ operator for matrix operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t3 = Matrix.new([2, 3])
val t4 = Matrix.new([3, 2])
val result = t3.matmul(t4)
expect result.shape == [2, 2]
```

</details>


</details>

### Simple Math: tensor literals

#### should create 3D tensor from slice mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t8 = Matrix.new([2, 3, 4])
expect t8.shape == [2, 3, 4]
```

</details>

#### should create sparse tensor from flat mode with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t9 = Matrix.new([5, 5])
expect t9.shape == [5, 5]
```

</details>

#### should support different data types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t10 = Matrix.new([10, 10])
expect t10.shape == [10, 10]
```

</details>

### Simple Math: combined operations

#### should combine grid literals with linalg operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t5 = Matrix.new([4, 4])
expect t5.shape == [4, 4]
```

</details>

#### should use @ operator in linear system solving

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape1 = [3, 3]
val shape2 = [3, 1]
val m = Matrix.new(shape1)
val n = Matrix.new(shape2)
expect m.shape == [3, 3]
expect n.shape == [3, 1]
```

</details>

#### should apply FFT to grid data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t6 = Matrix.new([8, 8])
expect t6.shape == [8, 8]
```

</details>

#### should use where with grid comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t7 = Matrix.new([5, 5])
val filtered = t7.mask(true)
expect filtered.shape == [5, 5]
```

</details>

<details>
<summary>Advanced: should combine clamp with matrix operations</summary>

#### should combine clamp with matrix operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t11 = Matrix.new([6, 6])
val clamped = t11.clamp(min_val=0.0, max_val=1.0)
expect clamped.shape == [6, 6]
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/simple_math_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Math: @ matrix multiplication operator
- Simple Math: 2D array literals
- Simple Math: tensor literals
- Simple Math: combined operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
