# Tensor Operations Specification

> Tensor operations for mathematical computing:

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
| Source | `test/feature/usage/tensor_spec.spl` |
| Updated | 2026-08-26 |
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

- is alias for Tensor<T, 2>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is alias for Tensor<T, 2>")
val A = zeros<f64>([3, 4], Device.cpu())
expect A.ndim == 2
```

</details>

#### Vector<T>

#### is alias for Tensor<T, 1>

- is alias for Tensor<T, 1>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is alias for Tensor<T, 1>")
val x = zeros<f64>([5], Device.cpu())
expect x.ndim == 1
```

</details>

#### concrete aliases

<details>
<summary>Advanced: provides Mat as Matrix<f64></summary>

#### provides Mat as Matrix<f64>

- provides Mat as Matrix<f64>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("provides Mat as Matrix<f64>")
val A = zeros<f64>([2, 3], Device.cpu())
expect A.shape == [2, 3]
```

</details>


</details>

#### provides Vec as Vector<f64>

- provides Vec as Vector<f64>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("provides Vec as Vector<f64>")
val x = ones<f64>([4], Device.cpu())
expect x.shape == [4]
```

</details>

### Transpose Operators

#### property transpose .T

<details>
<summary>Advanced: transposes 2D matrix</summary>

#### transposes 2D matrix

- transposes 2D matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transposes 2D matrix")
val A = [[1, 2, 3], [4, 5, 6]]
val At = A.T
expect At.shape == [3, 2]
expect At[0][0] == 1
expect At[0][1] == 4
```

</details>


</details>

#### is equivalent to .t()

- is equivalent to .t()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is equivalent to .t()")
val A = [[1, 2], [3, 4]]
expect A.T == A.t()
```

</details>

#### postfix transpose ' in m{}

<details>
<summary>Advanced: transposes matrix</summary>

#### transposes matrix

- transposes matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transposes matrix")
val A = [[1, 2], [3, 4]]
val At = m{ A' }
expect At == [[1, 3], [2, 4]]
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("transposes matrix")<br>
> val A = [[1, 2], [3, 4]]<br>
> val At = $A^{T}$<br>
> expect At == [[1, 3], [2, 4]]

</details>

</details>


</details>

#### chains with matmul

- chains with matmul


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains with matmul")
val A = [[1, 2], [3, 4]]
val x = [1, 1]
val y = m{ A' @ x }
expect y == [4, 6]
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("chains with matmul")<br>
> val A = [[1, 2], [3, 4]]<br>
> val x = [1, 1]<br>
> val y = $A^{T}$<br>
> expect y == [4, 6]

</details>

</details>

#### works in complex expressions

- works in complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in complex expressions")
val A = [[1, 0], [0, 1]]
val b = [1, 2]
# (A'A)^-1 A'b for A=I is just b
val result = m{ (A' @ A) @ A' @ b }
expect result == [1, 2]
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works in complex expressions")<br>
> val A = [[1, 0], [0, 1]]<br>
> val b = [1, 2]<br>
> # (A'A)^-1 A'b for A=I is just b<br>
> val result = $(A^{T})$<br>
> expect result == [1, 2]

</details>

</details>

#### general transpose

#### swaps specified dimensions

- swaps specified dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("swaps specified dimensions")
val T = zeros<f64>([2, 3, 4])
val Tt = T.transpose(0, 2)
expect Tt.shape == [4, 3, 2]
```

</details>

#### permutes multiple dimensions

- permutes multiple dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("permutes multiple dimensions")
val T = zeros<f64>([2, 3, 4, 5])
val Tp = T.permute([3, 1, 2, 0])
expect Tp.shape == [5, 3, 4, 2]
```

</details>

### Global Reductions

#### sum

#### sums all elements

- sums all elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums all elements")
val x = [1.0, 2.0, 3.0, 4.0]
expect x.sum == 10.0
```

</details>

<details>
<summary>Advanced: sums matrix elements</summary>

#### sums matrix elements

- sums matrix elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums matrix elements")
val A = [[1, 2], [3, 4]]
expect A.sum == 10
```

</details>


</details>

#### mean

#### computes mean

- computes mean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes mean")
val x = [1.0, 2.0, 3.0, 4.0]
expect x.mean == 2.5
```

</details>

#### product

#### multiplies all elements

- multiplies all elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies all elements")
val x = [1.0, 2.0, 3.0, 4.0]
expect x.prod == 24.0
```

</details>

#### min/max

#### finds minimum

- finds minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds minimum")
val x = [3.0, 1.0, 4.0, 1.0, 5.0]
expect x.min == 1.0
```

</details>

#### finds maximum

- finds maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds maximum")
val x = [3.0, 1.0, 4.0, 1.0, 5.0]
expect x.max == 5.0
```

</details>

#### standard deviation

#### computes std

- computes std


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes std")
val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
expect x.std.approx(2.0, epsilon: 0.1)
```

</details>

#### variance

#### computes var

- computes var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes var")
val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
expect x.var.approx(4.0, epsilon: 0.1)
```

</details>

#### norm

#### computes L2 norm

- computes L2 norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes L2 norm")
val x = [3.0, 4.0]
expect x.norm() == 5.0
```

</details>

#### computes L1 norm

- computes L1 norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes L1 norm")
val x = [3.0, -4.0]
expect x.norm(1) == 7.0
```

</details>

### Axis Reductions

#### sum along axis

#### sums columns (axis=0)

- sums columns (axis=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums columns (axis=0)")
val A = [[1, 2], [3, 4], [5, 6]]
expect A.sum(axis: 0) == [9, 12]
```

</details>

#### sums rows (axis=1)

- sums rows (axis=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums rows (axis=1)")
val A = [[1, 2], [3, 4], [5, 6]]
expect A.sum(axis: 1) == [3, 7, 11]
```

</details>

#### keeps dimension with keepdim

- keeps dimension with keepdim


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps dimension with keepdim")
val A = [[1, 2], [3, 4]]
val s = A.sum(axis: 0, keepdim: true)
expect s.shape == [1, 2]
```

</details>

#### mean along axis

#### means columns

- means columns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("means columns")
val A = [[1.0, 2.0], [3.0, 4.0]]
expect A.mean(axis: 0) == [2.0, 3.0]
```

</details>

#### min/max along axis

#### finds min with indices

- finds min with indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds min with indices")
val A = [[3, 1], [4, 2]]
val (vals, idx) = A.min(axis: 1)
expect vals == [1, 2]
expect idx == [1, 1]
```

</details>

#### finds max with indices

- finds max with indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds max with indices")
val A = [[3, 1], [4, 2]]
val (vals, idx) = A.max(axis: 1)
expect vals == [3, 4]
expect idx == [0, 0]
```

</details>

#### argmin/argmax

#### returns indices of min

- returns indices of min


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns indices of min")
val A = [[3, 1, 4], [1, 5, 9]]
expect A.argmin(axis: 1) == [1, 0]
```

</details>

#### returns indices of max

- returns indices of max


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns indices of max")
val A = [[3, 1, 4], [1, 5, 9]]
expect A.argmax(axis: 1) == [2, 2]
```

</details>

### Axis-Aware Slicing

#### single axis slice

#### slices first axis

- slices first axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("slices first axis")
val A = [[1, 2, 3], [4, 5, 6]]
expect A[0] == [1, 2, 3]
```

</details>

#### slices second axis

- slices second axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("slices second axis")
val A = [[1, 2, 3], [4, 5, 6]]
expect A.column(0) == [1, 4]
```

</details>

#### range slices

#### slices range on both axes

- slices range on both axes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("slices range on both axes")
val A = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
expect A[0:2].map(_1[1:3]) == [[2, 3], [5, 6]]
```

</details>

#### ellipsis

#### expands to fill dimensions

- expands to fill dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("expands to fill dimensions")
val T = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]  # 2x2x2
expect T.map(_1.column(0)) == [[1, 3], [5, 7]]
expect T[0] == [[1, 2], [3, 4]]
```

</details>

#### step slicing

#### takes every nth element

- takes every nth element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("takes every nth element")
val x = [0, 1, 2, 3, 4, 5]
expect x[::2] == [0, 2, 4]
```

</details>

#### reverses via .reversed(), not a negative-step slice

- reverses via .reversed(), not a negative-step slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reverses via .reversed(), not a negative-step slice")
val x = [0, 1, 2, 3, 4, 5]
expect x.reversed() == [5, 4, 3, 2, 1, 0]
```

</details>

### Shape Manipulation

#### reshape

#### reshapes to new dimensions

- reshapes to new dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reshapes to new dimensions")
val A = [[1, 2, 3], [4, 5, 6]]
expect A.reshape([6]).shape == [6]
expect A.reshape([3, 2]).shape == [3, 2]
```

</details>

#### infers dimension with -1

- infers dimension with -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers dimension with -1")
val A = [[1, 2, 3], [4, 5, 6]]
expect A.reshape([-1]).shape == [6]
expect A.reshape([3, -1]).shape == [3, 2]
```

</details>

#### squeeze

#### removes size-1 dimensions

- removes size-1 dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("removes size-1 dimensions")
val A = zeros<f64>([1, 3, 1, 4])
expect A.squeeze().shape == [3, 4]
```

</details>

#### removes specific dimension

- removes specific dimension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("removes specific dimension")
val A = zeros<f64>([1, 3, 1, 4])
expect A.squeeze(0).shape == [3, 1, 4]
```

</details>

#### unsqueeze

#### adds dimension at position

- adds dimension at position


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds dimension at position")
val x = [1, 2, 3]
expect x.unsqueeze(0).shape == [1, 3]
expect x.unsqueeze(1).shape == [3, 1]
```

</details>

### Tensor Construction

#### zeros/ones

#### creates zero tensor

- creates zero tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates zero tensor")
val A = zeros<f64>([2, 3])
expect A.sum == 0.0
```

</details>

#### creates ones tensor

- creates ones tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates ones tensor")
val A = ones<f64>([2, 3])
expect A.sum == 6.0
```

</details>

#### eye

<details>
<summary>Advanced: creates identity matrix</summary>

#### creates identity matrix

- creates identity matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates identity matrix")
val I = eye<f64>(3)
expect I[0][0] == 1.0
expect I[0][1] == 0.0
expect I.trace() == 3.0
```

</details>


</details>

#### arange

#### creates range tensor

- creates range tensor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates range tensor")
val x = arange(0, 5, 1)
expect x == [0, 1, 2, 3, 4]
```

</details>

#### creates stepped range

- creates stepped range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates stepped range")
val x = arange(0, 10, 2)
expect x == [0, 2, 4, 6, 8]
```

</details>

#### linspace

#### creates linearly spaced values

- creates linearly spaced values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates linearly spaced values")
val x = linspace(0.0, 1.0, 5)
expect x[0] == 0.0
expect x[4] == 1.0
expect x.len() == 5
```

</details>

### Elementwise Math

#### basic functions

#### computes absolute value

- computes absolute value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes absolute value")
val x = [-1.0, 2.0, -3.0]
expect x.abs() == [1.0, 2.0, 3.0]
```

</details>

#### computes square root

- computes square root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes square root")
val x = [1.0, 4.0, 9.0]
expect x.sqrt() == [1.0, 2.0, 3.0]
```

</details>

#### computes exponential

- computes exponential


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes exponential")
val x = [0.0, 1.0]
expect x.exp()[0].approx(1.0)
expect x.exp()[1].approx(2.718, epsilon: 0.01)
```

</details>

#### trigonometric

#### computes sin/cos

- computes sin/cos


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes sin/cos")
val x = [0.0]
expect x.sin()[0].approx(0.0)
expect x.cos()[0].approx(1.0)
```

</details>

#### clamp

#### clamps to range

- clamps to range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clamps to range")
val x = [-1.0, 0.5, 2.0]
expect x.clamp(min: 0.0, max: 1.0) == [0.0, 0.5, 1.0]
```

</details>

### Linear Algebra

#### determinant

#### computes 2x2 determinant

- computes 2x2 determinant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes 2x2 determinant")
val A = [[1.0, 2.0], [3.0, 4.0]]
expect A.det().approx(-2.0)
```

</details>

#### inverse

<details>
<summary>Advanced: computes matrix inverse</summary>

#### computes matrix inverse

- computes matrix inverse


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes matrix inverse")
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

- solves linear system


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("solves linear system")
val A = [[2.0, 1.0], [1.0, 3.0]]
val b = [4.0, 5.0]
val x = A.solve(b)
expect (A @ x)[0].approx(4.0)
expect (A @ x)[1].approx(5.0)
```

</details>

#### trace

#### sums diagonal elements

- sums diagonal elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sums diagonal elements")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7102e162d7b96426d8e6695880e3ba1afc0db493934f3c31edda94c91c9f2e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7102e162d7b96426d8e6695880e3ba1afc0db493934f3c31edda94c91c9f2e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7102e162d7b96426d8e6695880e3ba1afc0db493934f3c31edda94c91c9f2e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/tensor_spec.spl
mirror: doc/06_spec/feature/usage/tensor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/tensor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/tensor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/tensor_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is alias for Tensor<T, 2>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/tensor_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is alias for Tensor<T, 1>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/tensor_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides Mat as Matrix<f64>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
