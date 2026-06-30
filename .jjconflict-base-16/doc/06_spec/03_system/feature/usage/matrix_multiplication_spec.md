# Matrix Multiplication Operator (@)

> Matrix multiplication is implemented in the interpreter with proper dimension checking

<!-- sdn-diagram:id=matrix_multiplication_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=matrix_multiplication_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

matrix_multiplication_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=matrix_multiplication_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matrix Multiplication Operator (@)

Matrix multiplication is implemented in the interpreter with proper dimension checking

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | OP-MATMUL |
| Category | Operators \| Linear Algebra |
| Status | Implemented |
| Source | `test/03_system/feature/usage/matrix_multiplication_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Matrix Multiplication - Scalar Operations

#### multiplies two integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3 @ 4
expect result == 12
```

</details>

#### multiplies two floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.5 @ 4.0
expect result == 10.0
```

</details>

#### handles mixed int/float (int @ float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3 @ 2.5
expect result == 7.5
```

</details>

#### handles mixed int/float (float @ int)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.5 @ 3
expect result == 7.5
```

</details>

#### handles zero multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0 @ 100
expect result == 0
```

</details>

#### handles negative numbers

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-3) @ 4
expect result == (-12)
```

</details>

#### handles negative floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-2.5) @ (-4.0)
expect result == 10.0
```

</details>

### Matrix Multiplication - Dot Product (1D @ 1D)

#### computes dot product of integer vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [4, 5, 6]
val result = a @ b
expect result == 32  # 1*4 + 2*5 + 3*6 = 32
```

</details>

#### computes dot product of float vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1.0, 2.0, 3.0]
val b = [4.0, 5.0, 6.0]
val result = a @ b
expect result == 32.0
```

</details>

#### computes dot product with mixed int/float

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [1.5, 2.5, 3.5]
val result = a @ b
expect result == 17.0  # 1*1.5 + 2*2.5 + 3*3.5
```

</details>

#### handles zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [0, 0, 0]
val result = a @ b
expect result == 0
```

</details>

#### handles single element vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [5]
val b = [3]
val result = a @ b
expect result == 15
```

</details>

#### handles negative vectors

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, -2, 3]
val b = [-4, 5, -6]
val result = a @ b
expect result == (-32)  # 1*(-4) + (-2)*5 + 3*(-6) = -32
```

</details>

#### handles orthogonal vectors (dot product = 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 0]
val b = [0, 1]
val result = a @ b
expect result == 0
```

</details>

#### computes dot product of longer vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3, 4, 5]
val b = [2, 3, 4, 5, 6]
val result = a @ b
expect result == 70  # 2 + 6 + 12 + 20 + 30
```

</details>

### Matrix Multiplication - 2D @ 2D

#### multiplies 2x2 matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val b = [[5, 6], [7, 8]]
val c = a @ b
expect c == [[19, 22], [43, 50]]
```

</details>

#### multiplies 2x3 and 3x2 matrices

1. expect c[0] len
2. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2, 3], [4, 5, 6]]
val b = [[7, 8], [9, 10], [11, 12]]
val c = a @ b
expect c[0].len() == 2
expect c.len() == 2
expect c[0][0] == 58
expect c[0][1] == 64
expect c[1][0] == 139
expect c[1][1] == 154
```

</details>

<details>
<summary>Advanced: multiplies identity matrix</summary>

#### multiplies identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity = [[1, 0], [0, 1]]
val a = [[3, 4], [5, 6]]
val result = identity @ a
expect result == a
```

</details>


</details>

#### multiplies 3x3 identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
val b = [[2, 3, 4], [5, 6, 7], [8, 9, 10]]
val c = a @ b
expect c == b
```

</details>

#### handles 1x1 matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[5]]
val b = [[3]]
val c = a @ b
expect c == [[15]]
```

</details>

#### handles rectangular matrices (tall @ wide)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1], [2], [3]]  # 3x1
val b = [[4, 5, 6]]      # 1x3
val c = a @ b            # 3x3
expect c == [[4, 5, 6], [8, 10, 12], [12, 15, 18]]
```

</details>

<details>
<summary>Advanced: handles zero matrix</summary>

#### handles zero matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val zero = [[0, 0], [0, 0]]
val c = a @ zero
expect c == [[0, 0], [0, 0]]
```

</details>


</details>

#### handles negative matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val b = [[-1, 0], [0, -1]]
val c = a @ b
expect c == [[-1, -2], [-3, -4]]
```

</details>

### Matrix Multiplication - Matrix-Vector

<details>
<summary>Advanced: multiplies 2x3 matrix by 3x1 vector</summary>

#### multiplies 2x3 matrix by 3x1 vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2, 3], [4, 5, 6]]
val b = [7, 8, 9]
val c = a @ b
expect c == [50, 122]
```

</details>


</details>

<details>
<summary>Advanced: multiplies 3x2 matrix by 2x1 vector</summary>

#### multiplies 3x2 matrix by 2x1 vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4], [5, 6]]
val b = [10, 20]
val c = a @ b
expect c == [50, 110, 170]
```

</details>


</details>

<details>
<summary>Advanced: multiplies identity matrix by vector</summary>

#### multiplies identity matrix by vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
val v = [5, 10, 15]
val result = identity @ v
expect result == v
```

</details>


</details>

<details>
<summary>Advanced: multiplies vector by matrix (1x2 @ 2x3)</summary>

#### multiplies vector by matrix (1x2 @ 2x3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2]
val b = [[3, 4, 5], [6, 7, 8]]
val c = a @ b
expect c == [15, 18, 21]
```

</details>


</details>

<details>
<summary>Advanced: multiplies vector by identity matrix</summary>

#### multiplies vector by identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = [5, 10]
val identity = [[1, 0], [0, 1]]
val result = v @ identity
expect result == v
```

</details>


</details>

<details>
<summary>Advanced: handles single column matrix</summary>

#### handles single column matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = [[1], [2], [3]]
val v = [4]
val result = m @ v
expect result == [4, 8, 12]
```

</details>


</details>

### Matrix Multiplication - Float Promotion

<details>
<summary>Advanced: promotes int matrix to float when multiplied with float matrix</summary>

#### promotes int matrix to float when multiplied with float matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val b = [[1.5, 2.5], [3.5, 4.5]]
val c = a @ b
val expected = [[8.5, 11.5], [18.5, 25.5]]
expect c == expected
```

</details>


</details>

#### promotes int vector to float when multiplied with float vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [1.5, 2.5, 3.5]
val result = a @ b
expect result == 17.0
```

</details>

<details>
<summary>Advanced: handles mixed int/float matrix-vector</summary>

#### handles mixed int/float matrix-vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = [[1, 2], [3, 4]]
val v = [1.5, 2.5]
val result = m @ v
expect result == [6.5, 14.5]
```

</details>


</details>

### Matrix Multiplication - Special Matrices

#### multiplies diagonal matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[2, 0], [0, 3]]
val b = [[4, 0], [0, 5]]
val c = a @ b
expect c == [[8, 0], [0, 15]]
```

</details>

#### multiplies upper triangular matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [0, 3]]
val b = [[4, 5], [0, 6]]
val c = a @ b
expect c == [[4, 17], [0, 18]]
```

</details>

<details>
<summary>Advanced: multiplies symmetric matrix</summary>

#### multiplies symmetric matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [2, 1]]
val b = [[3, 4], [4, 3]]
val c = a @ b
expect c == [[11, 10], [10, 11]]
```

</details>


</details>

### Matrix Multiplication - Mathematical Properties

#### satisfies associativity: (A @ B) @ C == A @ (B @ C)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val b = [[5, 6], [7, 8]]
val c = [[9, 10], [11, 12]]
val left = (a @ b) @ c
val right = a @ (b @ c)
expect left == right
```

</details>

#### is NOT commutative: A @ B != B @ A (in general)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [[1, 2], [3, 4]]
val b = [[5, 6], [7, 8]]
val ab = a @ b
val ba = b @ a
expect ab != ba
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
