# Tensor Operations Specification

> Tensor operations for mathematical computing:

<!-- sdn-diagram:id=tensor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Operations Specification

Tensor operations for mathematical computing:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2210-2230 |
| Category | Syntax / Stdlib |
| Status | Implemented |
| Source | `test/03_system/feature/usage/tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tensor operations for mathematical computing:
- Tensor<T, N>, Matrix<T>, Vector<T> type aliases
- Transpose operators (' in m{}, .T outside)
- Reduction operations (sum, mean, std, etc.)
- Axis-aware operations

## Scenarios

### Tensor Type Aliases

#### Matrix<T>

#### is alias for Tensor<T, 2>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = zeros<f64>([3, 4], Device.cpu())
expect A.ndim == 2
```

</details>

#### Vector<T>

#### is alias for Tensor<T, 1>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = zeros<f64>([5], Device.cpu())
expect x.ndim == 1
```

</details>

#### concrete aliases

<details>
<summary>Advanced: provides Mat as Matrix<f64></summary>

#### provides Mat as Matrix<f64>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = zeros<f64>([2, 3], Device.cpu())
expect A.shape == [2, 3]
```

</details>


</details>

#### provides Vec as Vector<f64>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ones<f64>([4], Device.cpu())
expect x.shape == [4]
```

</details>

### Transpose Operators

#### property transpose .T

<details>
<summary>Advanced: transposes 2D matrix</summary>

#### transposes 2D matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6]]
val At = A.T
expect At.shape == [3, 2]
expect At[0][0] == 1
expect At[0][1] == 4
```

</details>


</details>

#### is equivalent to .t()

1. expect A T == A t


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
expect A.T == A.t()
```

</details>

#### postfix transpose ' in m{}

<details>
<summary>Advanced: transposes matrix</summary>

#### transposes matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
val At = m{ A' }
expect At == [[1, 3], [2, 4]]
```

<details>
<summary>Rendered scenario source</summary>

> val A = [[1, 2], [3, 4]]<br>
> val At = $A^{T}$<br>
> expect At == [[1, 3], [2, 4]]

</details>

</details>


</details>

#### chains with matmul

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
val x = [1, 1]
val y = m{ A' @ x }
expect y == [4, 6]
```

<details>
<summary>Rendered scenario source</summary>

> val A = [[1, 2], [3, 4]]<br>
> val x = [1, 1]<br>
> val y = $A^{T}$<br>
> expect y == [4, 6]

</details>

</details>

#### works in complex expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 0], [0, 1]]
val b = [1, 2]
# (A'A)^-1 A'b for A=I is just b
val result = m{ (A' @ A) @ A' @ b }
expect result == [1, 2]
```

<details>
<summary>Rendered scenario source</summary>

> val A = [[1, 0], [0, 1]]<br>
> val b = [1, 2]<br>
> # (A'A)^-1 A'b for A=I is just b<br>
> val result = $(A^{T})$<br>
> expect result == [1, 2]

</details>

</details>

#### general transpose

#### swaps specified dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val T = zeros<f64>([2, 3, 4])
val Tt = T.transpose(0, 2)
expect Tt.shape == [4, 3, 2]
```

</details>

#### permutes multiple dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val T = zeros<f64>([2, 3, 4, 5])
val Tp = T.permute([3, 1, 2, 0])
expect Tp.shape == [5, 3, 4, 2]
```

</details>

### Global Reductions

#### sum

#### sums all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1.0, 2.0, 3.0, 4.0]
expect x.sum == 10.0
```

</details>

<details>
<summary>Advanced: sums matrix elements</summary>

#### sums matrix elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
expect A.sum == 10
```

</details>


</details>

#### mean

#### computes mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1.0, 2.0, 3.0, 4.0]
expect x.mean == 2.5
```

</details>

#### product

#### multiplies all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1.0, 2.0, 3.0, 4.0]
expect x.prod == 24.0
```

</details>

#### min/max

#### finds minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [3.0, 1.0, 4.0, 1.0, 5.0]
expect x.min == 1.0
```

</details>

#### finds maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [3.0, 1.0, 4.0, 1.0, 5.0]
expect x.max == 5.0
```

</details>

#### standard deviation

#### computes std

1. expect x std approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
expect x.std.approx(2.0, epsilon: 0.1)
```

</details>

#### variance

#### computes var

1. expect x var approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
expect x.var.approx(4.0, epsilon: 0.1)
```

</details>

#### norm

#### computes L2 norm

1. expect x norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [3.0, 4.0]
expect x.norm() == 5.0
```

</details>

#### computes L1 norm

1. expect x norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [3.0, -4.0]
expect x.norm(1) == 7.0
```

</details>

### Axis Reductions

#### sum along axis

#### sums columns (axis=0)

1. expect A sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4], [5, 6]]
expect A.sum(axis: 0) == [9, 12]
```

</details>

#### sums rows (axis=1)

1. expect A sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4], [5, 6]]
expect A.sum(axis: 1) == [3, 7, 11]
```

</details>

#### keeps dimension with keepdim

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
val s = A.sum(axis: 0, keepdim: true)
expect s.shape == [1, 2]
```

</details>

#### mean along axis

#### means columns

1. expect A mean


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1.0, 2.0], [3.0, 4.0]]
expect A.mean(axis: 0) == [2.0, 3.0]
```

</details>

#### min/max along axis

#### finds min with indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[3, 1], [4, 2]]
val (vals, idx) = A.min(axis: 1)
expect vals == [1, 2]
expect idx == [1, 1]
```

</details>

#### finds max with indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[3, 1], [4, 2]]
val (vals, idx) = A.max(axis: 1)
expect vals == [3, 4]
expect idx == [0, 0]
```

</details>

#### argmin/argmax

#### returns indices of min

1. expect A argmin


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[3, 1, 4], [1, 5, 9]]
expect A.argmin(axis: 1) == [1, 0]
```

</details>

#### returns indices of max

1. expect A argmax


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[3, 1, 4], [1, 5, 9]]
expect A.argmax(axis: 1) == [2, 2]
```

</details>

### Axis-Aware Slicing

#### single axis slice

#### slices first axis

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6]]
expect A[0] == [1, 2, 3]
```

</details>

#### slices second axis

1. expect A column


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6]]
expect A.column(0) == [1, 4]
```

</details>

#### range slices

#### slices range on both axes

1. expect A[0:2] map


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
expect A[0:2].map(_1[1:3]) == [[2, 3], [5, 6]]
```

</details>

#### ellipsis

#### expands to fill dimensions

1. expect T map


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val T = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]  # 2x2x2
expect T.map(_1.column(0)) == [[1, 3], [5, 7]]
expect T[0] == [[1, 2], [3, 4]]
```

</details>

#### step slicing

#### takes every nth element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [0, 1, 2, 3, 4, 5]
expect x[::2] == [0, 2, 4]
```

</details>

#### reverses with negative step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [0, 1, 2, 3, 4, 5]
expect x[::-1] == [5, 4, 3, 2, 1, 0]
```

</details>

### Shape Manipulation

#### reshape

#### reshapes to new dimensions

1. expect A reshape
2. expect A reshape


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6]]
expect A.reshape([6]).shape == [6]
expect A.reshape([3, 2]).shape == [3, 2]
```

</details>

#### infers dimension with -1

1. expect A reshape
2. expect A reshape


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2, 3], [4, 5, 6]]
expect A.reshape([-1]).shape == [6]
expect A.reshape([3, -1]).shape == [3, 2]
```

</details>

#### squeeze

#### removes size-1 dimensions

1. expect A squeeze


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = zeros<f64>([1, 3, 1, 4])
expect A.squeeze().shape == [3, 4]
```

</details>

#### removes specific dimension

1. expect A squeeze


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = zeros<f64>([1, 3, 1, 4])
expect A.squeeze(0).shape == [3, 1, 4]
```

</details>

#### unsqueeze

#### adds dimension at position

1. expect x unsqueeze
2. expect x unsqueeze


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1, 2, 3]
expect x.unsqueeze(0).shape == [1, 3]
expect x.unsqueeze(1).shape == [3, 1]
```

</details>

### Tensor Construction

#### zeros/ones

#### creates zero tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = zeros<f64>([2, 3])
expect A.sum == 0.0
```

</details>

#### creates ones tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = ones<f64>([2, 3])
expect A.sum == 6.0
```

</details>

#### eye

<details>
<summary>Advanced: creates identity matrix</summary>

#### creates identity matrix

1. expect I trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val I = eye<f64>(3)
expect I[0][0] == 1.0
expect I[0][1] == 0.0
expect I.trace() == 3.0
```

</details>


</details>

#### arange

#### creates range tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = arange(0, 5, 1)
expect x == [0, 1, 2, 3, 4]
```

</details>

#### creates stepped range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = arange(0, 10, 2)
expect x == [0, 2, 4, 6, 8]
```

</details>

#### linspace

#### creates linearly spaced values

1. expect x len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = linspace(0.0, 1.0, 5)
expect x[0] == 0.0
expect x[4] == 1.0
expect x.len() == 5
```

</details>

### Elementwise Math

#### basic functions

#### computes absolute value

1. expect x abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [-1.0, 2.0, -3.0]
expect x.abs() == [1.0, 2.0, 3.0]
```

</details>

#### computes square root

1. expect x sqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1.0, 4.0, 9.0]
expect x.sqrt() == [1.0, 2.0, 3.0]
```

</details>

#### computes exponential

1. expect x exp
2. expect x exp


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [0.0, 1.0]
expect x.exp()[0].approx(1.0)
expect x.exp()[1].approx(2.718, epsilon: 0.01)
```

</details>

#### trigonometric

#### computes sin/cos

1. expect x sin
2. expect x cos


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [0.0]
expect x.sin()[0].approx(0.0)
expect x.cos()[0].approx(1.0)
```

</details>

#### clamp

#### clamps to range

1. expect x clamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [-1.0, 0.5, 2.0]
expect x.clamp(min: 0.0, max: 1.0) == [0.0, 0.5, 1.0]
```

</details>

### Linear Algebra

#### determinant

#### computes 2x2 determinant

1. expect A det


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1.0, 2.0], [3.0, 4.0]]
expect A.det().approx(-2.0)
```

</details>

#### inverse

<details>
<summary>Advanced: computes matrix inverse</summary>

#### computes matrix inverse

1. expect I[0][0] approx
2. expect I[0][1] approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1.0, 2.0], [3.0, 4.0]]
val Ainv = A.inv()
val I = A @ Ainv
expect I[0][0].approx(1.0)
expect I[0][1].approx(0.0)
```

</details>


</details>

#### solve

#### solves linear system

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[2.0, 1.0], [1.0, 3.0]]
val b = [4.0, 5.0]
val x = A.solve(b)
expect (A @ x)[0].approx(4.0)
expect (A @ x)[1].approx(5.0)
```

</details>

#### trace

#### sums diagonal elements

1. expect A trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val A = [[1, 2], [3, 4]]
expect A.trace() == 5
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
