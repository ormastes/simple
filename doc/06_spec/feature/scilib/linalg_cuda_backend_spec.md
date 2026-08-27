# Linalg CUDA Backend Specification

> Purpose: Verify linalg CUDA dynamic backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg CUDA Backend Specification

Purpose: Verify linalg CUDA dynamic backend.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-002, REQ-SCILIB-C-004, REQ-SCILIB-C-005, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/linalg_cuda_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify linalg CUDA dynamic backend.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### linalg CUDA dynamic backend

#### reports either an available CUDA backend or a typed unavailable error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports either an available CUDA backend or a typed unavailable error
- reports either an available CUDA backend or a typed unavailable error
   - Expected: status.selected equals `cuda`
   - Expected: status.available is true
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports either an available CUDA backend or a typed unavailable error")
step("reports either an available CUDA backend or a typed unavailable error")
# @req: REQ-SCILIB-C-002
# @req: REQ-SCILIB-C-004
# @req: REQ-SCILIB-C-005
val required = require_linalg_backend("cuda")
match required:
    case Ok(status):
        expect(status.selected).to_equal("cuda")
        expect(status.available).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar dot when the CUDA shim is available

- matches scalar dot when the CUDA shim is available
- matches scalar dot when the CUDA shim is available
   - Expected: value equals `dot(left, right).unwrap()`
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar dot when the CUDA shim is available")
step("matches scalar dot when the CUDA shim is available")
val left = vector_from([Float64.new(1.5), Float64.new(-2.0), Float64.new(3.25), Float64.new(4.0)])
val right = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(-1.0), Float64.new(0.5)])
val result = cuda_dot(left, right)
match result:
    case Ok(value):
        expect(value).to_equal(dot(left, right).unwrap())
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured

- keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured
- keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured
   - Expected: dot(left, right).unwrap() equals `Float64.new(32.0)`
   - Expected: gemv_result.get_f64(Index.new(0)) equals `Float64.new(32.0)`
   - Expected: gemv_result.get_f64(Index.new(1)) equals `Float64.new(77.0)`
   - Expected: gemm_result.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(58.0)`
   - Expected: gemm_result.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(64.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(139.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(154.0)`
   - Expected: solve_result.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: solve_result.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: inv_result.rows() equals `Index.new(16)`
   - Expected: inv_result.cols() equals `Index.new(16)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(15), Index.new(15)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(15)]) equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured")
step("keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured")
val left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
expect(dot(left, right).unwrap()).to_equal(Float64.new(32.0))

val matrix = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val gemv_result = gemv(matrix, right).unwrap()
expect(gemv_result.get_f64(Index.new(0))).to_equal(Float64.new(32.0))
expect(gemv_result.get_f64(Index.new(1))).to_equal(Float64.new(77.0))

val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = zeros_matrix(Index.new(2), Index.new(2))
val gemm_result = gemm(Float64.new(1.0), matrix, b, Float64.new(0.0), c_in)
expect(gemm_result.get_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(58.0))
expect(gemm_result.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(64.0))
expect(gemm_result.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(139.0))
expect(gemm_result.get_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(154.0))

val solve_a = matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(2.0)]])
val solve_b = vector_from([Float64.new(9.0), Float64.new(8.0)])
val solve_result = solve(solve_a, solve_b).unwrap()
expect(solve_result.get_f64(Index.new(0))).to_equal(Float64.new(2.0))
expect(solve_result.get_f64(Index.new(1))).to_equal(Float64.new(3.0))

val inv_input = eye_matrix(Index.new(16))
val inv_result = inv(inv_input).unwrap()
expect(inv_result.rows()).to_equal(Index.new(16))
expect(inv_result.cols()).to_equal(Index.new(16))
expect(inv_result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(inv_result.get_f64_at([Index.new(15), Index.new(15)])).to_equal(Float64.new(1.0))
expect(inv_result.get_f64_at([Index.new(0), Index.new(15)])).to_equal(Float64.new(0.0))
```

</details>

#### returns a typed error for shape mismatches before backend execution

- returns a typed error for shape mismatches before backend execution
- returns a typed error for shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for shape mismatches before backend execution")
step("returns a typed error for shape mismatches before backend execution")
val result = cuda_dot_values([Float64.new(1.0)], [Float64.new(1.0), Float64.new(2.0)])
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("same-length")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar gemm when the CUDA shim is available

- matches scalar gemm when the CUDA shim is available
- matches scalar gemm when the CUDA shim is available
   - Expected: value.get_at([Index.new(0), Index.new(0)]) equals `scalar.get_at([Index.new(0), Index.new(0)])`
   - Expected: value.get_at([Index.new(0), Index.new(1)]) equals `scalar.get_at([Index.new(0), Index.new(1)])`
   - Expected: value.get_at([Index.new(1), Index.new(0)]) equals `scalar.get_at([Index.new(1), Index.new(0)])`
   - Expected: value.get_at([Index.new(1), Index.new(1)]) equals `scalar.get_at([Index.new(1), Index.new(1)])`
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar gemm when the CUDA shim is available")
step("matches scalar gemm when the CUDA shim is available")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val result = cuda_gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
match result:
    case Ok(value):
        val scalar = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
        expect(value.get_at([Index.new(0), Index.new(0)])).to_equal(scalar.get_at([Index.new(0), Index.new(0)]))
        expect(value.get_at([Index.new(0), Index.new(1)])).to_equal(scalar.get_at([Index.new(0), Index.new(1)]))
        expect(value.get_at([Index.new(1), Index.new(0)])).to_equal(scalar.get_at([Index.new(1), Index.new(0)]))
        expect(value.get_at([Index.new(1), Index.new(1)])).to_equal(scalar.get_at([Index.new(1), Index.new(1)]))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for gemm shape mismatches before backend execution

- returns a typed error for gemm shape mismatches before backend execution
- returns a typed error for gemm shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for gemm shape mismatches before backend execution")
step("returns a typed error for gemm shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = matrix_from_rows([[Float64.new(3.0), Float64.new(4.0)]])
val c_in = zeros_matrix(Index.new(1), Index.new(2))
val result = cuda_gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar gemv when the CUDA shim is available

- matches scalar gemv when the CUDA shim is available
- matches scalar gemv when the CUDA shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar gemv when the CUDA shim is available")
step("matches scalar gemv when the CUDA shim is available")
val matrix = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val vector = vector_from([Float64.new(7.0), Float64.new(8.0), Float64.new(9.0)])
val y_in = vector_from([Float64.new(1.0), Float64.new(2.0)])
val result = cuda_gemv(Float64.new(2.0), matrix, vector, Float64.new(3.0), y_in)
match result:
    case Ok(value):
        val scalar = gemv(matrix, vector).unwrap().mul_scalar(Float64.new(2.0)).add(y_in.mul_scalar(Float64.new(3.0)))
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for gemv shape mismatches before backend execution

- returns a typed error for gemv shape mismatches before backend execution
- returns a typed error for gemv shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for gemv shape mismatches before backend execution")
step("returns a typed error for gemv shape mismatches before backend execution")
val matrix = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val vector = vector_from([Float64.new(3.0)])
val y_in = vector_from([Float64.new(0.0)])
val result = cuda_gemv(Float64.new(1.0), matrix, vector, Float64.new(0.0), y_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar solve when the CUDA shim is available

- matches scalar solve when the CUDA shim is available
- matches scalar solve when the CUDA shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar solve when the CUDA shim is available")
step("matches scalar solve when the CUDA shim is available")
val a = matrix_from_rows([
    [Float64.new(3.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(2.0)]])
val b = vector_from([Float64.new(9.0), Float64.new(8.0)])
val result = cuda_solve(a, b)
match result:
    case Ok(value):
        val scalar = solve(a, b).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for solve shape mismatches before backend execution

- returns a typed error for solve shape mismatches before backend execution
- returns a typed error for solve shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for solve shape mismatches before backend execution")
step("returns a typed error for solve shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = vector_from([Float64.new(3.0)])
val result = cuda_solve(a, b)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square")
    case _:
        expect(false).to_equal(true)
```

</details>

#### matches scalar inverse when the CUDA shim is available

- matches scalar inverse when the CUDA shim is available
- matches scalar inverse when the CUDA shim is available
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar inverse when the CUDA shim is available")
step("matches scalar inverse when the CUDA shim is available")
val a = matrix_from_rows([
    [Float64.new(4.0), Float64.new(7.0)],
    [Float64.new(2.0), Float64.new(6.0)]])
val result = cuda_inv(a)
match result:
    case Ok(value):
        val v00 = value.get_f64_at([Index.new(0), Index.new(0)]).value
        val v01 = value.get_f64_at([Index.new(0), Index.new(1)]).value
        val v10 = value.get_f64_at([Index.new(1), Index.new(0)]).value
        val v11 = value.get_f64_at([Index.new(1), Index.new(1)]).value
        expect(v00).to_be_greater_than(0.599)
        expect(v00).to_be_less_than(0.601)
        expect(v01).to_be_greater_than(-0.701)
        expect(v01).to_be_less_than(-0.699)
        expect(v10).to_be_greater_than(-0.201)
        expect(v10).to_be_less_than(-0.199)
        expect(v11).to_be_greater_than(0.399)
        expect(v11).to_be_less_than(0.401)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns a typed error for inverse shape mismatches before backend execution

- returns a typed error for inverse shape mismatches before backend execution
- returns a typed error for inverse shape mismatches before backend execution
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed error for inverse shape mismatches before backend execution")
step("returns a typed error for inverse shape mismatches before backend execution")
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val result = cuda_inv(a)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square")
    case _:
        expect(false).to_equal(true)
```

</details>

### Fortran ABI smoke tests (pure-Simple, no FFI)

#### LP64 integer width is 8 bytes

- LP64 integer width is 8 bytes
- LP64 integer width is 8 bytes
   - Expected: lp64_bytes equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("LP64 integer width is 8 bytes")
step("LP64 integer width is 8 bytes")
# The scilib shim uses int64_t for all index/info arguments.
# This constant must equal 8 for the LP64 ABI contract to hold.
val lp64_bytes: i64 = 8
expect(lp64_bytes).to_equal(8)
```

</details>

#### row-major to column-major index conversion is correct

- row-major to column-major index conversion is correct
- row-major to column-major index conversion is correct
   - Expected: rm_idx equals `6`
   - Expected: cm_idx equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("row-major to column-major index conversion is correct")
step("row-major to column-major index conversion is correct")
# For a 3×4 matrix stored row-major:
#   element (row=1, col=2) is at flat offset row*cols + col = 1*4 + 2 = 6
# The same element in column-major (lda = nrows = 3) is at col*lda + row = 2*3 + 1 = 7
val rows = 3
val cols = 4
val row = 1
val col = 2
val rm_idx = row * cols + col
val cm_idx = col * rows + row
expect(rm_idx).to_equal(6)
expect(cm_idx).to_equal(7)
```

</details>

#### operand-swap identity: (A*B)^T = B^T * A^T for 2x2 case

- operand-swap identity: (A*B)^T = B^T * A^T for 2x2 case
- operand-swap identity: (A*B)^T = B^T * A^T for 2x2 case
   - Expected: ct_00 equals `btat_00`
   - Expected: ct_01 equals `btat_01`
   - Expected: ct_10 equals `btat_10`
   - Expected: ct_11 equals `btat_11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("operand-swap identity: (A*B)^T = B^T * A^T for 2x2 case")
step("operand-swap identity: (A*B)^T = B^T * A^T for 2x2 case")
# Verify the Layer B operand-swap trick arithmetically:
# A = [[1,2],[3,4]], B = [[5,6],[7,8]]
# C = A*B:
#   C[0,0] = 1*5 + 2*7 = 19
#   C[0,1] = 1*6 + 2*8 = 22
#   C[1,0] = 3*5 + 4*7 = 43
#   C[1,1] = 3*6 + 4*8 = 50
# C^T:
#   CT[0,0] = C[0,0] = 19
#   CT[0,1] = C[1,0] = 43
#   CT[1,0] = C[0,1] = 22
#   CT[1,1] = C[1,1] = 50
# B^T * A^T, where B^T=[[5,7],[6,8]], A^T=[[1,3],[2,4]]:
#   [0,0] = 5*1 + 7*2 = 19  ← same as CT[0,0]
#   [0,1] = 5*3 + 7*4 = 43  ← same as CT[0,1]
#   [1,0] = 6*1 + 8*2 = 22  ← same as CT[1,0]
#   [1,1] = 6*3 + 8*4 = 50  ← same as CT[1,1]
val c_00 = 1 * 5 + 2 * 7
val c_01 = 1 * 6 + 2 * 8
val c_10 = 3 * 5 + 4 * 7
val c_11 = 3 * 6 + 4 * 8
# C^T elements (transposed indices)
val ct_00 = c_00
val ct_01 = c_10
val ct_10 = c_01
val ct_11 = c_11
# B^T * A^T elements
val btat_00 = 5 * 1 + 7 * 2
val btat_01 = 5 * 3 + 7 * 4
val btat_10 = 6 * 1 + 8 * 2
val btat_11 = 6 * 3 + 8 * 4
# (A*B)^T == B^T*A^T element-wise
expect(ct_00).to_equal(btat_00)
expect(ct_01).to_equal(btat_01)
expect(ct_10).to_equal(btat_10)
expect(ct_11).to_equal(btat_11)
```

</details>

#### blas symbol names follow rt_blas_ prefix convention

- blas symbol names follow rt_blas_ prefix convention
- blas symbol names follow rt_blas_ prefix convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("blas symbol names follow rt_blas_ prefix convention")
step("blas symbol names follow rt_blas_ prefix convention")
# Canonical names as returned by the shim — no trailing underscore.
val dgemm = "rt_blas_dgemm"
val ddot = "rt_blas_ddot"
val daxpy = "rt_blas_daxpy"
val sgemm = "rt_blas_sgemm"
expect(dgemm).to_start_with("rt_blas_d")
expect(ddot).to_start_with("rt_blas_d")
expect(daxpy).to_start_with("rt_blas_d")
expect(sgemm).to_start_with("rt_blas_s")
expect(dgemm).to_end_with("gemm")
expect(ddot).to_end_with("dot")
```

</details>

#### lapack symbol names follow rt_lapack_d prefix convention

- lapack symbol names follow rt_lapack_d prefix convention
- lapack symbol names follow rt_lapack_d prefix convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lapack symbol names follow rt_lapack_d prefix convention")
step("lapack symbol names follow rt_lapack_d prefix convention")
val dgesv = "rt_lapack_dgesv"
val dgetrf = "rt_lapack_dgetrf"
val dgetrs = "rt_lapack_dgetrs"
expect(dgesv).to_start_with("rt_lapack_d")
expect(dgetrf).to_start_with("rt_lapack_d")
expect(dgetrs).to_start_with("rt_lapack_d")
```

</details>

#### pivot index conversion: 1-based to 0-based is correct

- pivot index conversion: 1-based to 0-based is correct
- pivot index conversion: 1-based to 0-based is correct
   - Expected: simple_pivot equals `2`
   - Expected: back_to_lapack equals `lapack_pivot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pivot index conversion: 1-based to 0-based is correct")
step("pivot index conversion: 1-based to 0-based is correct")
# LAPACK/cuSOLVER return 1-based IPIV; Simple uses 0-based.
val lapack_pivot: i64 = 3
val simple_pivot = lapack_pivot - 1
expect(simple_pivot).to_equal(2)
# Round-trip: 0-based back to 1-based
val back_to_lapack = simple_pivot + 1
expect(back_to_lapack).to_equal(lapack_pivot)
```

</details>

#### BLAS transpose flags match scilib shim contract

- BLAS transpose flags match scilib shim contract
- BLAS transpose flags match scilib shim contract
   - Expected: op_n equals `0`
   - Expected: op_t equals `1`
   - Expected: op_c equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("BLAS transpose flags match scilib shim contract")
step("BLAS transpose flags match scilib shim contract")
# scilib shim: 0 = no-transpose, 1 = transpose, 2 = conjugate-transpose
val op_n: i64 = 0
val op_t: i64 = 1
val op_c: i64 = 2
expect(op_n).to_equal(0)
expect(op_t).to_equal(1)
expect(op_c).to_equal(2)
# For real matrices, op_c == op_t
expect(op_c).to_be_greater_than(op_t - 1)
```

</details>

### CUDA provider selection (pure-Simple, no FFI)

#### selects mock when requested explicitly regardless of availability

- selects mock when requested explicitly regardless of availability
- selects mock when requested explicitly regardless of availability
   - Expected: selected equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects mock when requested explicitly regardless of availability")
step("selects mock when requested explicitly regardless of availability")
# Mock is always available.
val requested = "mock"
var selected = "mock"
if requested == "cuda":
    selected = "cuda"
if requested == "openblas":
    selected = "openblas"
expect(selected).to_equal("mock")
```

</details>

#### selects mock fallback when cuda requested but unavailable

- selects mock fallback when cuda requested but unavailable
- selects mock fallback when cuda requested but unavailable
   - Expected: selected equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects mock fallback when cuda requested but unavailable")
step("selects mock fallback when cuda requested but unavailable")
val requested = "cuda"
val cuda_available: bool = false
var selected = "mock"
if requested == "cuda" and cuda_available:
    selected = "cuda"
expect(selected).to_equal("mock")
```

</details>

#### selects cuda when requested and available

- selects cuda when requested and available
- selects cuda when requested and available
   - Expected: selected equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects cuda when requested and available")
step("selects cuda when requested and available")
val requested = "cuda"
val cuda_available: bool = true
var selected = "mock"
if requested == "cuda" and cuda_available:
    selected = "cuda"
expect(selected).to_equal("cuda")
```

</details>

#### auto-selects cuda over openblas when both available

- auto-selects cuda over openblas when both available
- auto-selects cuda over openblas when both available
   - Expected: selected equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("auto-selects cuda over openblas when both available")
step("auto-selects cuda over openblas when both available")
val cuda_available: bool = true
val openblas_available: bool = true
var selected = "mock"
if cuda_available:
    selected = "cuda"
else:
    if openblas_available:
        selected = "openblas"
expect(selected).to_equal("cuda")
```

</details>

#### auto-selects openblas when cuda unavailable but openblas available

- auto-selects openblas when cuda unavailable but openblas available
- auto-selects openblas when cuda unavailable but openblas available
   - Expected: selected equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("auto-selects openblas when cuda unavailable but openblas available")
step("auto-selects openblas when cuda unavailable but openblas available")
val cuda_available: bool = false
val openblas_available: bool = true
var selected = "mock"
if cuda_available:
    selected = "cuda"
else:
    if openblas_available:
        selected = "openblas"
expect(selected).to_equal("openblas")
```

</details>

#### auto-selects mock when neither cuda nor openblas available

- auto-selects mock when neither cuda nor openblas available
- auto-selects mock when neither cuda nor openblas available
   - Expected: selected equals `mock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("auto-selects mock when neither cuda nor openblas available")
step("auto-selects mock when neither cuda nor openblas available")
val cuda_available: bool = false
val openblas_available: bool = false
var selected = "mock"
if cuda_available:
    selected = "cuda"
else:
    if openblas_available:
        selected = "openblas"
expect(selected).to_equal("mock")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-SCILIB-C-002`
- `REQ-SCILIB-C-004`
- `REQ-SCILIB-C-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45e5a0667b377ba65bb6823be05a3583d33115926d8e984cf9b1c92502e0e86d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45e5a0667b377ba65bb6823be05a3583d33115926d8e984cf9b1c92502e0e86d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45e5a0667b377ba65bb6823be05a3583d33115926d8e984cf9b1c92502e0e86d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/linalg_cuda_backend_spec.spl
mirror: doc/06_spec/feature/scilib/linalg_cuda_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/linalg_cuda_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/linalg_cuda_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/linalg_cuda_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/linalg_cuda_backend_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports either an available CUDA backend or a typed unavailable error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_cuda_backend_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches scalar dot when the CUDA shim is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_cuda_backend_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
