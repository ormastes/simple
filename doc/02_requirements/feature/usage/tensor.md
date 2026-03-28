# Tensor Operations Specification
*Source:* `test/feature/usage/tensor_spec.spl`
**Feature IDs:** #2210-2230  |  **Category:** Syntax / Stdlib  |  **Status:** Implemented

## Overview




Tensor operations for mathematical computing:
- Tensor<T, N>, Matrix<T>, Vector<T> type aliases
- Transpose operators (' in m{}, .T outside)
- Reduction operations (sum, mean, std, etc.)
- Axis-aware operations

## Feature: Tensor Type Aliases

Type aliases for common tensor ranks.

### Scenario: Matrix<T>

| # | Example | Status |
|---|---------|--------|
| 1 | is alias for Tensor<T, 2> | pass |

**Example:** is alias for Tensor<T, 2>
    Given val A: Matrix<f64> = zeros<f64>([3, 4])
    Then  expect A.ndim == 2

### Scenario: Vector<T>

| # | Example | Status |
|---|---------|--------|
| 1 | is alias for Tensor<T, 1> | pass |

**Example:** is alias for Tensor<T, 1>
    Given val x: Vector<f64> = zeros<f64>([5])
    Then  expect x.ndim == 1

### Scenario: concrete aliases

| # | Example | Status |
|---|---------|--------|
| 1 | provides Mat as Matrix<f64> | pass |
| 2 | provides Vec as Vector<f64> | pass |

**Example:** provides Mat as Matrix<f64>
    Given val A: Mat = zeros<f64>([2, 3])
    Then  expect A.shape == [2, 3]

**Example:** provides Vec as Vector<f64>
    Given val x: Vec = ones<f64>([4])
    Then  expect x.shape == [4]

## Feature: Transpose Operators

Transpose operations:
    - ' (postfix) inside m{} blocks
    - .T / .t() outside m{} blocks

### Scenario: property transpose .T

| # | Example | Status |
|---|---------|--------|
| 1 | transposes 2D matrix | pass |
| 2 | is equivalent to .t() | pass |

**Example:** transposes 2D matrix
    Given val A = [[1, 2, 3], [4, 5, 6]]
    Given val At = A.T
    Then  expect At.shape == [3, 2]
    Then  expect At[0][0] == 1
    Then  expect At[0][1] == 4

**Example:** is equivalent to .t()
    Given val A = [[1, 2], [3, 4]]
    Then  expect A.T == A.t()

### Scenario: postfix transpose ' in m{}

| # | Example | Status |
|---|---------|--------|
| 1 | transposes matrix | pass |
| 2 | chains with matmul | pass |
| 3 | works in complex expressions | pass |

**Example:** transposes matrix
    Given val A = [[1, 2], [3, 4]]
    Given val At = m{ A' }
    Then  expect At == [[1, 3], [2, 4]]

**Example:** chains with matmul
    Given val A = [[1, 2], [3, 4]]
    Given val x = [1, 1]
    Given val y = m{ A' @ x }
    Then  expect y == [4, 6]

**Example:** works in complex expressions
    Given val A = [[1, 0], [0, 1]]
    Given val b = [1, 2]
    Given val result = m{ (A' @ A) @ A' @ b }
    Then  expect result == [1, 2]

### Scenario: general transpose

| # | Example | Status |
|---|---------|--------|
| 1 | swaps specified dimensions | pass |
| 2 | permutes multiple dimensions | pass |

**Example:** swaps specified dimensions
    Given val T = zeros<f64>([2, 3, 4])
    Given val Tt = T.transpose(0, 2)
    Then  expect Tt.shape == [4, 3, 2]

**Example:** permutes multiple dimensions
    Given val T = zeros<f64>([2, 3, 4, 5])
    Given val Tp = T.permute([3, 1, 2, 0])
    Then  expect Tp.shape == [5, 3, 4, 2]

## Feature: Global Reductions

Reduction operations over all elements.

### Scenario: sum

| # | Example | Status |
|---|---------|--------|
| 1 | sums all elements | pass |
| 2 | sums matrix elements | pass |

**Example:** sums all elements
    Given val x = [1.0, 2.0, 3.0, 4.0]
    Then  expect x.sum == 10.0

**Example:** sums matrix elements
    Given val A = [[1, 2], [3, 4]]
    Then  expect A.sum == 10

### Scenario: mean

| # | Example | Status |
|---|---------|--------|
| 1 | computes mean | pass |

**Example:** computes mean
    Given val x = [1.0, 2.0, 3.0, 4.0]
    Then  expect x.mean == 2.5

### Scenario: product

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies all elements | pass |

**Example:** multiplies all elements
    Given val x = [1.0, 2.0, 3.0, 4.0]
    Then  expect x.prod == 24.0

### Scenario: min/max

| # | Example | Status |
|---|---------|--------|
| 1 | finds minimum | pass |
| 2 | finds maximum | pass |

**Example:** finds minimum
    Given val x = [3.0, 1.0, 4.0, 1.0, 5.0]
    Then  expect x.min == 1.0

**Example:** finds maximum
    Given val x = [3.0, 1.0, 4.0, 1.0, 5.0]
    Then  expect x.max == 5.0

### Scenario: standard deviation

| # | Example | Status |
|---|---------|--------|
| 1 | computes std | pass |

**Example:** computes std
    Given val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
    Then  expect x.std.approx(2.0, epsilon: 0.1)

### Scenario: variance

| # | Example | Status |
|---|---------|--------|
| 1 | computes var | pass |

**Example:** computes var
    Given val x = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
    Then  expect x.var.approx(4.0, epsilon: 0.1)

### Scenario: norm

| # | Example | Status |
|---|---------|--------|
| 1 | computes L2 norm | pass |
| 2 | computes L1 norm | pass |

**Example:** computes L2 norm
    Given val x = [3.0, 4.0]
    Then  expect x.norm() == 5.0

**Example:** computes L1 norm
    Given val x = [3.0, -4.0]
    Then  expect x.norm(1) == 7.0

## Feature: Axis Reductions

Reduction operations along specific axes.

### Scenario: sum along axis

| # | Example | Status |
|---|---------|--------|
| 1 | sums columns (axis=0) | pass |
| 2 | sums rows (axis=1) | pass |
| 3 | keeps dimension with keepdim | pass |

**Example:** sums columns (axis=0)
    Given val A = [[1, 2], [3, 4], [5, 6]]
    Then  expect A.sum(axis: 0) == [9, 12]

**Example:** sums rows (axis=1)
    Given val A = [[1, 2], [3, 4], [5, 6]]
    Then  expect A.sum(axis: 1) == [3, 7, 11]

**Example:** keeps dimension with keepdim
    Given val A = [[1, 2], [3, 4]]
    Given val s = A.sum(axis: 0, keepdim: true)
    Then  expect s.shape == [1, 2]

### Scenario: mean along axis

| # | Example | Status |
|---|---------|--------|
| 1 | means columns | pass |

**Example:** means columns
    Given val A = [[1.0, 2.0], [3.0, 4.0]]
    Then  expect A.mean(axis: 0) == [2.0, 3.0]

### Scenario: min/max along axis

| # | Example | Status |
|---|---------|--------|
| 1 | finds min with indices | pass |
| 2 | finds max with indices | pass |

**Example:** finds min with indices
    Given val A = [[3, 1], [4, 2]]
    Given val (vals, idx) = A.min(axis: 1)
    Then  expect vals == [1, 2]
    Then  expect idx == [1, 1]

**Example:** finds max with indices
    Given val A = [[3, 1], [4, 2]]
    Given val (vals, idx) = A.max(axis: 1)
    Then  expect vals == [3, 4]
    Then  expect idx == [0, 0]

### Scenario: argmin/argmax

| # | Example | Status |
|---|---------|--------|
| 1 | returns indices of min | pass |
| 2 | returns indices of max | pass |

**Example:** returns indices of min
    Given val A = [[3, 1, 4], [1, 5, 9]]
    Then  expect A.argmin(axis: 1) == [1, 0]

**Example:** returns indices of max
    Given val A = [[3, 1, 4], [1, 5, 9]]
    Then  expect A.argmax(axis: 1) == [2, 2]

## Feature: Axis-Aware Slicing

Multi-dimensional slicing with :, ..., and ranges.

### Scenario: single axis slice

| # | Example | Status |
|---|---------|--------|
| 1 | slices first axis | pass |
| 2 | slices second axis | pass |

**Example:** slices first axis
    Given val A = [[1, 2, 3], [4, 5, 6]]
    Then  expect A[0] == [1, 2, 3]

**Example:** slices second axis
    Given val A = [[1, 2, 3], [4, 5, 6]]
    Then  expect A.column(0) == [1, 4]

### Scenario: range slices

| # | Example | Status |
|---|---------|--------|
| 1 | slices range on both axes | pass |

**Example:** slices range on both axes
    Given val A = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    Then  expect A[0:2].map(\row: row[1:3]) == [[2, 3], [5, 6]]

### Scenario: ellipsis

| # | Example | Status |
|---|---------|--------|
| 1 | expands to fill dimensions | pass |

**Example:** expands to fill dimensions
    Given val T = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]  # 2x2x2
    Then  expect T.map(\m: m.column(0)) == [[1, 3], [5, 7]]
    Then  expect T[0] == [[1, 2], [3, 4]]

### Scenario: step slicing

| # | Example | Status |
|---|---------|--------|
| 1 | takes every nth element | pass |
| 2 | reverses with negative step | pass |

**Example:** takes every nth element
    Given val x = [0, 1, 2, 3, 4, 5]
    Then  expect x[::2] == [0, 2, 4]

**Example:** reverses with negative step
    Given val x = [0, 1, 2, 3, 4, 5]
    Then  expect x[::-1] == [5, 4, 3, 2, 1, 0]

## Feature: Shape Manipulation

Reshape, squeeze, unsqueeze operations.

### Scenario: reshape

| # | Example | Status |
|---|---------|--------|
| 1 | reshapes to new dimensions | pass |
| 2 | infers dimension with -1 | pass |

**Example:** reshapes to new dimensions
    Given val A = [[1, 2, 3], [4, 5, 6]]
    Then  expect A.reshape([6]).shape == [6]
    Then  expect A.reshape([3, 2]).shape == [3, 2]

**Example:** infers dimension with -1
    Given val A = [[1, 2, 3], [4, 5, 6]]
    Then  expect A.reshape([-1]).shape == [6]
    Then  expect A.reshape([3, -1]).shape == [3, 2]

### Scenario: squeeze

| # | Example | Status |
|---|---------|--------|
| 1 | removes size-1 dimensions | pass |
| 2 | removes specific dimension | pass |

**Example:** removes size-1 dimensions
    Given val A = zeros<f64>([1, 3, 1, 4])
    Then  expect A.squeeze().shape == [3, 4]

**Example:** removes specific dimension
    Given val A = zeros<f64>([1, 3, 1, 4])
    Then  expect A.squeeze(0).shape == [3, 1, 4]

### Scenario: unsqueeze

| # | Example | Status |
|---|---------|--------|
| 1 | adds dimension at position | pass |

**Example:** adds dimension at position
    Given val x = [1, 2, 3]
    Then  expect x.unsqueeze(0).shape == [1, 3]
    Then  expect x.unsqueeze(1).shape == [3, 1]

## Feature: Tensor Construction

Factory functions for creating tensors.

### Scenario: zeros/ones

| # | Example | Status |
|---|---------|--------|
| 1 | creates zero tensor | pass |
| 2 | creates ones tensor | pass |

**Example:** creates zero tensor
    Given val A = zeros<f64>([2, 3])
    Then  expect A.sum == 0.0

**Example:** creates ones tensor
    Given val A = ones<f64>([2, 3])
    Then  expect A.sum == 6.0

### Scenario: eye

| # | Example | Status |
|---|---------|--------|
| 1 | creates identity matrix | pass |

**Example:** creates identity matrix
    Given val I = eye<f64>(3)
    Then  expect I[0][0] == 1.0
    Then  expect I[0][1] == 0.0
    Then  expect I.trace() == 3.0

### Scenario: arange

| # | Example | Status |
|---|---------|--------|
| 1 | creates range tensor | pass |
| 2 | creates stepped range | pass |

**Example:** creates range tensor
    Given val x = arange(0, 5, 1)
    Then  expect x == [0, 1, 2, 3, 4]

**Example:** creates stepped range
    Given val x = arange(0, 10, 2)
    Then  expect x == [0, 2, 4, 6, 8]

### Scenario: linspace

| # | Example | Status |
|---|---------|--------|
| 1 | creates linearly spaced values | pass |

**Example:** creates linearly spaced values
    Given val x = linspace(0.0, 1.0, 5)
    Then  expect x[0] == 0.0
    Then  expect x[4] == 1.0
    Then  expect x.len() == 5

## Feature: Elementwise Math

Elementwise mathematical functions.

### Scenario: basic functions

| # | Example | Status |
|---|---------|--------|
| 1 | computes absolute value | pass |
| 2 | computes square root | pass |
| 3 | computes exponential | pass |

**Example:** computes absolute value
    Given val x = [-1.0, 2.0, -3.0]
    Then  expect x.abs() == [1.0, 2.0, 3.0]

**Example:** computes square root
    Given val x = [1.0, 4.0, 9.0]
    Then  expect x.sqrt() == [1.0, 2.0, 3.0]

**Example:** computes exponential
    Given val x = [0.0, 1.0]
    Then  expect x.exp()[0].approx(1.0)
    Then  expect x.exp()[1].approx(2.718, epsilon: 0.01)

### Scenario: trigonometric

| # | Example | Status |
|---|---------|--------|
| 1 | computes sin/cos | pass |

**Example:** computes sin/cos
    Given val x = [0.0]
    Then  expect x.sin()[0].approx(0.0)
    Then  expect x.cos()[0].approx(1.0)

### Scenario: clamp

| # | Example | Status |
|---|---------|--------|
| 1 | clamps to range | pass |

**Example:** clamps to range
    Given val x = [-1.0, 0.5, 2.0]
    Then  expect x.clamp(min: 0.0, max: 1.0) == [0.0, 0.5, 1.0]

## Feature: Linear Algebra

Linear algebra operations.

### Scenario: determinant

| # | Example | Status |
|---|---------|--------|
| 1 | computes 2x2 determinant | pass |

**Example:** computes 2x2 determinant
    Given val A = [[1.0, 2.0], [3.0, 4.0]]
    Then  expect A.det().approx(-2.0)

### Scenario: inverse

| # | Example | Status |
|---|---------|--------|
| 1 | computes matrix inverse | pass |

**Example:** computes matrix inverse
    Given val A = [[1.0, 2.0], [3.0, 4.0]]
    Given val Ainv = A.inv()
    Given val I = A @ Ainv
    Then  expect I[0][0].approx(1.0)
    Then  expect I[0][1].approx(0.0)

### Scenario: solve

| # | Example | Status |
|---|---------|--------|
| 1 | solves linear system | pass |

**Example:** solves linear system
    Given val A = [[2.0, 1.0], [1.0, 3.0]]
    Given val b = [4.0, 5.0]
    Given val x = A.solve(b)
    Then  expect (A @ x)[0].approx(4.0)
    Then  expect (A @ x)[1].approx(5.0)

### Scenario: trace

| # | Example | Status |
|---|---------|--------|
| 1 | sums diagonal elements | pass |

**Example:** sums diagonal elements
    Given val A = [[1, 2], [3, 4]]
    Then  expect A.trace() == 5


