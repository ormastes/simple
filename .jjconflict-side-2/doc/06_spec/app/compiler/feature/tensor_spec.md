# Tensor Operations Specification

**Feature ID:** #2210-2230 | **Category:** Syntax / Stdlib | **Status:** Implemented

_Source: `test/feature/usage/tensor_spec.spl`_

---

Tensor operations for mathematical computing:
- Tensor<T, N>, Matrix<T>, Vector<T> type aliases
- Transpose operators (' in m{}, .T outside)
- Reduction operations (sum, mean, std, etc.)
- Axis-aware operations

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 55 |

## Test Structure

### Tensor Type Aliases

#### Matrix<T>

- ✅ is alias for Tensor<T, 2>
#### Vector<T>

- ✅ is alias for Tensor<T, 1>
#### concrete aliases

- ✅ provides Mat as Matrix<f64>
- ✅ provides Vec as Vector<f64>
### Transpose Operators

#### property transpose .T

- ✅ transposes 2D matrix
- ✅ is equivalent to .t()
#### postfix transpose ' in m{}

- ✅ transposes matrix
- ✅ chains with matmul
- ✅ works in complex expressions
#### general transpose

- ✅ swaps specified dimensions
- ✅ permutes multiple dimensions
### Global Reductions

#### sum

- ✅ sums all elements
- ✅ sums matrix elements
#### mean

- ✅ computes mean
#### product

- ✅ multiplies all elements
#### min/max

- ✅ finds minimum
- ✅ finds maximum
#### standard deviation

- ✅ computes std
#### variance

- ✅ computes var
#### norm

- ✅ computes L2 norm
- ✅ computes L1 norm
### Axis Reductions

#### sum along axis

- ✅ sums columns (axis=0)
- ✅ sums rows (axis=1)
- ✅ keeps dimension with keepdim
#### mean along axis

- ✅ means columns
#### min/max along axis

- ✅ finds min with indices
- ✅ finds max with indices
#### argmin/argmax

- ✅ returns indices of min
- ✅ returns indices of max
### Axis-Aware Slicing

#### single axis slice

- ✅ slices first axis
- ✅ slices second axis
#### range slices

- ✅ slices range on both axes
#### ellipsis

- ✅ expands to fill dimensions
#### step slicing

- ✅ takes every nth element
- ✅ reverses with negative step
### Shape Manipulation

#### reshape

- ✅ reshapes to new dimensions
- ✅ infers dimension with -1
#### squeeze

- ✅ removes size-1 dimensions
- ✅ removes specific dimension
#### unsqueeze

- ✅ adds dimension at position
### Tensor Construction

#### zeros/ones

- ✅ creates zero tensor
- ✅ creates ones tensor
#### eye

- ✅ creates identity matrix
#### arange

- ✅ creates range tensor
- ✅ creates stepped range
#### linspace

- ✅ creates linearly spaced values
### Elementwise Math

#### basic functions

- ✅ computes absolute value
- ✅ computes square root
- ✅ computes exponential
#### trigonometric

- ✅ computes sin/cos
#### clamp

- ✅ clamps to range
### Linear Algebra

#### determinant

- ✅ computes 2x2 determinant
#### inverse

- ✅ computes matrix inverse
#### solve

- ✅ solves linear system
#### trace

- ✅ sums diagonal elements

