# Matrix Multiplication Operator (@)
*Source:* `test/feature/usage/matrix_multiplication_spec.spl`
**Feature IDs:** OP-MATMUL  |  **Category:** Operators | Linear Algebra  |  **Status:** Implemented

## Overview



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

## Feature: Matrix Multiplication - Scalar Operations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies two integers | pass |
| 2 | multiplies two floats | pass |
| 3 | handles mixed int/float (int @ float) | pass |
| 4 | handles mixed int/float (float @ int) | pass |
| 5 | handles zero multiplication | pass |
| 6 | handles negative numbers | pass |
| 7 | handles negative floats | pass |

**Example:** multiplies two integers
    Given val result = 3 @ 4
    Then  expect result == 12

**Example:** multiplies two floats
    Given val result = 2.5 @ 4.0
    Then  expect result == 10.0

**Example:** handles mixed int/float (int @ float)
    Given val result = 3 @ 2.5
    Then  expect result == 7.5

**Example:** handles mixed int/float (float @ int)
    Given val result = 2.5 @ 3
    Then  expect result == 7.5

**Example:** handles zero multiplication
    Given val result = 0 @ 100
    Then  expect result == 0

**Example:** handles negative numbers
    Given val result = (-3) @ 4
    Then  expect result == (-12)

**Example:** handles negative floats
    Given val result = (-2.5) @ (-4.0)
    Then  expect result == 10.0

## Feature: Matrix Multiplication - Dot Product (1D @ 1D)

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | computes dot product of integer vectors | pass |
| 2 | computes dot product of float vectors | pass |
| 3 | computes dot product with mixed int/float | pass |
| 4 | handles zero vector | pass |
| 5 | handles single element vectors | pass |
| 6 | handles negative vectors | pass |
| 7 | handles orthogonal vectors (dot product = 0) | pass |
| 8 | computes dot product of longer vectors | pass |

**Example:** computes dot product of integer vectors
    Given val a = [1, 2, 3]
    Given val b = [4, 5, 6]
    Given val result = a @ b
    Then  expect result == 32  # 1*4 + 2*5 + 3*6 = 32

**Example:** computes dot product of float vectors
    Given val a = [1.0, 2.0, 3.0]
    Given val b = [4.0, 5.0, 6.0]
    Given val result = a @ b
    Then  expect result == 32.0

**Example:** computes dot product with mixed int/float
    Given val a = [1, 2, 3]
    Given val b = [1.5, 2.5, 3.5]
    Given val result = a @ b
    Then  expect result == 17.0  # 1*1.5 + 2*2.5 + 3*3.5

**Example:** handles zero vector
    Given val a = [1, 2, 3]
    Given val b = [0, 0, 0]
    Given val result = a @ b
    Then  expect result == 0

**Example:** handles single element vectors
    Given val a = [5]
    Given val b = [3]
    Given val result = a @ b
    Then  expect result == 15

**Example:** handles negative vectors
    Given val a = [1, -2, 3]
    Given val b = [-4, 5, -6]
    Given val result = a @ b
    Then  expect result == (-32)  # 1*(-4) + (-2)*5 + 3*(-6) = -32

**Example:** handles orthogonal vectors (dot product = 0)
    Given val a = [1, 0]
    Given val b = [0, 1]
    Given val result = a @ b
    Then  expect result == 0

**Example:** computes dot product of longer vectors
    Given val a = [1, 2, 3, 4, 5]
    Given val b = [2, 3, 4, 5, 6]
    Given val result = a @ b
    Then  expect result == 70  # 2 + 6 + 12 + 20 + 30

## Feature: Matrix Multiplication - 2D @ 2D

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies 2x2 matrices | pass |
| 2 | multiplies 2x3 and 3x2 matrices | pass |
| 3 | multiplies identity matrix | pass |
| 4 | multiplies 3x3 identity | pass |
| 5 | handles 1x1 matrices | pass |
| 6 | handles rectangular matrices (tall @ wide) | pass |
| 7 | handles zero matrix | pass |
| 8 | handles negative matrices | pass |

**Example:** multiplies 2x2 matrices
    Given val a = [[1, 2], [3, 4]]
    Given val b = [[5, 6], [7, 8]]
    Given val c = a @ b
    Then  expect c == [[19, 22], [43, 50]]

**Example:** multiplies 2x3 and 3x2 matrices
    Given val a = [[1, 2, 3], [4, 5, 6]]
    Given val b = [[7, 8], [9, 10], [11, 12]]
    Given val c = a @ b
    Then  expect c.len() == 2
    Then  expect c[0].len() == 2
    Then  expect c[0][0] == 58
    Then  expect c[0][1] == 64
    Then  expect c[1][0] == 139
    Then  expect c[1][1] == 154

**Example:** multiplies identity matrix
    Given val identity = [[1, 0], [0, 1]]
    Given val a = [[3, 4], [5, 6]]
    Given val result = identity @ a
    Then  expect result == a

**Example:** multiplies 3x3 identity
    Given val a = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    Given val b = [[2, 3, 4], [5, 6, 7], [8, 9, 10]]
    Given val c = a @ b
    Then  expect c == b

**Example:** handles 1x1 matrices
    Given val a = [[5]]
    Given val b = [[3]]
    Given val c = a @ b
    Then  expect c == [[15]]

**Example:** handles rectangular matrices (tall @ wide)
    Given val a = [[1], [2], [3]]  # 3x1
    Given val b = [[4, 5, 6]]      # 1x3
    Given val c = a @ b            # 3x3
    Then  expect c == [[4, 5, 6], [8, 10, 12], [12, 15, 18]]

**Example:** handles zero matrix
    Given val a = [[1, 2], [3, 4]]
    Given val zero = [[0, 0], [0, 0]]
    Given val c = a @ zero
    Then  expect c == [[0, 0], [0, 0]]

**Example:** handles negative matrices
    Given val a = [[1, 2], [3, 4]]
    Given val b = [[-1, 0], [0, -1]]
    Given val c = a @ b
    Then  expect c == [[-1, -2], [-3, -4]]

## Feature: Matrix Multiplication - Matrix-Vector

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies 2x3 matrix by 3x1 vector | pass |
| 2 | multiplies 3x2 matrix by 2x1 vector | pass |
| 3 | multiplies identity matrix by vector | pass |
| 4 | multiplies vector by matrix (1x2 @ 2x3) | pass |
| 5 | multiplies vector by identity matrix | pass |
| 6 | handles single column matrix | pass |

**Example:** multiplies 2x3 matrix by 3x1 vector
    Given val a = [[1, 2, 3], [4, 5, 6]]
    Given val b = [7, 8, 9]
    Given val c = a @ b
    Then  expect c == [50, 122]

**Example:** multiplies 3x2 matrix by 2x1 vector
    Given val a = [[1, 2], [3, 4], [5, 6]]
    Given val b = [10, 20]
    Given val c = a @ b
    Then  expect c == [50, 110, 170]

**Example:** multiplies identity matrix by vector
    Given val identity = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    Given val v = [5, 10, 15]
    Given val result = identity @ v
    Then  expect result == v

**Example:** multiplies vector by matrix (1x2 @ 2x3)
    Given val a = [1, 2]
    Given val b = [[3, 4, 5], [6, 7, 8]]
    Given val c = a @ b
    Then  expect c == [15, 18, 21]

**Example:** multiplies vector by identity matrix
    Given val v = [5, 10]
    Given val identity = [[1, 0], [0, 1]]
    Given val result = v @ identity
    Then  expect result == v

**Example:** handles single column matrix
    Given val m = [[1], [2], [3]]
    Given val v = [4]
    Given val result = m @ v
    Then  expect result == [4, 8, 12]

## Feature: Matrix Multiplication - Float Promotion

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | promotes int matrix to float when multiplied with float matrix | pass |
| 2 | promotes int vector to float when multiplied with float vector | pass |
| 3 | handles mixed int/float matrix-vector | pass |

**Example:** promotes int matrix to float when multiplied with float matrix
    Given val a = [[1, 2], [3, 4]]
    Given val b = [[1.5, 2.5], [3.5, 4.5]]
    Given val c = a @ b
    Given val expected = [[8.5, 11.5], [18.5, 25.5]]
    Then  expect c == expected

**Example:** promotes int vector to float when multiplied with float vector
    Given val a = [1, 2, 3]
    Given val b = [1.5, 2.5, 3.5]
    Given val result = a @ b
    Then  expect result == 17.0

**Example:** handles mixed int/float matrix-vector
    Given val m = [[1, 2], [3, 4]]
    Given val v = [1.5, 2.5]
    Given val result = m @ v
    Then  expect result == [6.5, 14.5]

## Feature: Matrix Multiplication - Special Matrices

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies diagonal matrices | pass |
| 2 | multiplies upper triangular matrices | pass |
| 3 | multiplies symmetric matrix | pass |

**Example:** multiplies diagonal matrices
    Given val a = [[2, 0], [0, 3]]
    Given val b = [[4, 0], [0, 5]]
    Given val c = a @ b
    Then  expect c == [[8, 0], [0, 15]]

**Example:** multiplies upper triangular matrices
    Given val a = [[1, 2], [0, 3]]
    Given val b = [[4, 5], [0, 6]]
    Given val c = a @ b
    Then  expect c == [[4, 17], [0, 18]]

**Example:** multiplies symmetric matrix
    Given val a = [[1, 2], [2, 1]]
    Given val b = [[3, 4], [4, 3]]
    Given val c = a @ b
    Then  expect c == [[11, 10], [10, 11]]

## Feature: Matrix Multiplication - Mathematical Properties

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | satisfies associativity: (A @ B) @ C == A @ (B @ C) | pass |
| 2 | is NOT commutative: A @ B != B @ A (in general) | pass |

**Example:** satisfies associativity: (A @ B) @ C == A @ (B @ C)
    Given val a = [[1, 2], [3, 4]]
    Given val b = [[5, 6], [7, 8]]
    Given val c = [[9, 10], [11, 12]]
    Given val left = (a @ b) @ c
    Given val right = a @ (b @ c)
    Then  expect left == right

**Example:** is NOT commutative: A @ B != B @ A (in general)
    Given val a = [[1, 2], [3, 4]]
    Given val b = [[5, 6], [7, 8]]
    Given val ab = a @ b
    Given val ba = b @ a
    Then  expect ab != ba


