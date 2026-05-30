# Matrix Multiplication Operator (@)

**Feature ID:** OP-MATMUL | **Category:** Operators | Linear Algebra | **Status:** Implemented

_Source: `test/feature/usage/matrix_multiplication_spec.spl`_

---

## Implementation Details

Matrix multiplication is implemented in the interpreter with proper dimension checking
and automatic float/int promotion. Codegen mode delegates to the interpreter.

## Examples

```simple
# Scalars
val result = 3 @ 4  # 12

# Dot product
val v1 = [1, 2, 3]
val v2 = [4, 5, 6]
val dot = v1 @ v2  # 32

# Matrix multiplication
val a = [[1, 2], [3, 4]]
val b = [[5, 6], [7, 8]]
val c = a @ b  # [[19, 22], [43, 50]]

# Matrix-vector
val m = [[1, 2, 3], [4, 5, 6]]
val v = [7, 8, 9]
val result = m @ v  # [50, 122]
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 37 |

## Test Structure

### Matrix Multiplication - Scalar Operations
_Tests scalar @ scalar operations_

- ✅ multiplies two integers
- ✅ multiplies two floats
- ✅ handles mixed int/float (int @ float)
- ✅ handles mixed int/float (float @ int)
- ✅ handles zero multiplication
- ✅ handles negative numbers
- ✅ handles negative floats
### Matrix Multiplication - Dot Product (1D @ 1D)
_Tests 1D array dot products_

- ✅ computes dot product of integer vectors
- ✅ computes dot product of float vectors
- ✅ computes dot product with mixed int/float
- ✅ handles zero vector
- ✅ handles single element vectors
- ✅ handles negative vectors
- ✅ handles orthogonal vectors (dot product = 0)
- ✅ computes dot product of longer vectors
### Matrix Multiplication - 2D @ 2D
_Tests matrix @ matrix operations_

- ✅ multiplies 2x2 matrices
- ✅ multiplies 2x3 and 3x2 matrices
- ✅ multiplies identity matrix
- ✅ multiplies 3x3 identity
- ✅ handles 1x1 matrices
- ✅ handles rectangular matrices (tall @ wide)
- ✅ handles zero matrix
- ✅ handles negative matrices
### Matrix Multiplication - Matrix-Vector
_Tests matrix @ vector operations_

- ✅ multiplies 2x3 matrix by 3x1 vector
- ✅ multiplies 3x2 matrix by 2x1 vector
- ✅ multiplies identity matrix by vector
- ✅ multiplies vector by matrix (1x2 @ 2x3)
- ✅ multiplies vector by identity matrix
- ✅ handles single column matrix
### Matrix Multiplication - Float Promotion
_Tests automatic int/float promotion_

- ✅ promotes int matrix to float when multiplied with float matrix
- ✅ promotes int vector to float when multiplied with float vector
- ✅ handles mixed int/float matrix-vector
### Matrix Multiplication - Special Matrices
_Tests special matrix properties_

- ✅ multiplies diagonal matrices
- ✅ multiplies upper triangular matrices
- ✅ multiplies symmetric matrix
### Matrix Multiplication - Mathematical Properties
_Tests that @ satisfies expected mathematical properties_

- ✅ satisfies associativity: (A @ B) @ C == A @ (B @ C)
- ✅ is NOT commutative: A @ B != B @ A (in general)

