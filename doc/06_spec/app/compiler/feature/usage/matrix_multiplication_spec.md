# Matrix Multiplication Operator (@)

The `@` operator performs matrix multiplication following NumPy semantics:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | OP-MATMUL |
| Category | Operators \| Linear Algebra |
| Status | Implemented |
| Source | `test/feature/usage/matrix_multiplication_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

The `@` operator performs matrix multiplication following NumPy semantics:
- Scalar @ Scalar: Element-wise multiplication
- 1D @ 1D: Dot product (inner product)
- 2D @ 2D: Matrix multiplication
- 2D @ 1D: Matrix-vector product
- 1D @ 2D: Vector-matrix product

## Implementation Details

Matrix multiplication is implemented in the interpreter with proper dimension checking
and automatic float/int promotion. Codegen mode delegates to the interpreter.

## Examples

```simple
val result = 3 @ 4  # 12

val v1 = [1, 2, 3]
val v2 = [4, 5, 6]
val dot = v1 @ v2  # 32

val a = [[1, 2], [3, 4]]
val b = [[5, 6], [7, 8]]
val c = a @ b  # [[19, 22], [43, 50]]

val m = [[1, 2, 3], [4, 5, 6]]
val v = [7, 8, 9]
val result = m @ v  # [50, 122]
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/matrix_multiplication/result.json` |

## Scenarios

- multiplies two integers
- multiplies two floats
- handles mixed int/float (int @ float)
- handles mixed int/float (float @ int)
- handles zero multiplication
- handles negative numbers
- handles negative floats
- computes dot product of integer vectors
- computes dot product of float vectors
- computes dot product with mixed int/float
- handles zero vector
- handles single element vectors
- handles negative vectors
- handles orthogonal vectors (dot product = 0)
- computes dot product of longer vectors
- multiplies 2x2 matrices
- multiplies 2x3 and 3x2 matrices
- multiplies identity matrix
- multiplies 3x3 identity
- handles 1x1 matrices
- handles rectangular matrices (tall @ wide)
- handles zero matrix
- handles negative matrices
- multiplies 2x3 matrix by 3x1 vector
- multiplies 3x2 matrix by 2x1 vector
- multiplies identity matrix by vector
- multiplies vector by matrix (1x2 @ 2x3)
- multiplies vector by identity matrix
- handles single column matrix
- promotes int matrix to float when multiplied with float matrix
- promotes int vector to float when multiplied with float vector
- handles mixed int/float matrix-vector
- multiplies diagonal matrices
- multiplies upper triangular matrices
- multiplies symmetric matrix
- satisfies associativity: (A @ B) @ C == A @ (B @ C)
- is NOT commutative: A @ B != B @ A (in general)
