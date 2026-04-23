# Tensor Operations Specification

Tensor operations for mathematical computing:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2210-2230 |
| Category | Syntax / Stdlib |
| Status | Implemented |
| Source | `test/feature/usage/tensor_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tensor operations for mathematical computing:
- Tensor<T, N>, Matrix<T>, Vector<T> type aliases
- Transpose operators (' in m{}, .T outside)
- Reduction operations (sum, mean, std, etc.)
- Axis-aware operations

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/tensor/result.json` |

## Scenarios

- is alias for Tensor<T, 2>
- is alias for Tensor<T, 1>
- provides Mat as Matrix<f64>
- provides Vec as Vector<f64>
- transposes 2D matrix
- is equivalent to .t()
- transposes matrix
- chains with matmul
- works in complex expressions
- swaps specified dimensions
- permutes multiple dimensions
- sums all elements
- sums matrix elements
- computes mean
- multiplies all elements
- finds minimum
- finds maximum
- computes std
- computes var
- computes L2 norm
- computes L1 norm
- sums columns (axis=0)
- sums rows (axis=1)
- keeps dimension with keepdim
- means columns
- finds min with indices
- finds max with indices
- returns indices of min
- returns indices of max
- slices first axis
- slices second axis
- slices range on both axes
- expands to fill dimensions
- takes every nth element
- reverses with negative step
- reshapes to new dimensions
- infers dimension with -1
- removes size-1 dimensions
- removes specific dimension
- adds dimension at position
- creates zero tensor
- creates ones tensor
- creates identity matrix
- creates range tensor
- creates stepped range
- creates linearly spaced values
- computes absolute value
- computes square root
- computes exponential
- computes sin/cos
- clamps to range
- computes 2x2 determinant
- computes matrix inverse
- solves linear system
- sums diagonal elements
