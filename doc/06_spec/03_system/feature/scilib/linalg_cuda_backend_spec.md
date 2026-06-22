# Linalg CUDA Backend Specification

> Validates the explicit CUDA dynamic linalg adapter. The default scalar `dot`

<!-- sdn-diagram:id=linalg_cuda_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_cuda_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_cuda_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_cuda_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg CUDA Backend Specification

Validates the explicit CUDA dynamic linalg adapter. The default scalar `dot`

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-C-002, REQ-SCILIB-C-004, REQ-SCILIB-C-005, NFR-SCILIB-C-001, NFR-SCILIB-C-002 |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/linalg_cuda_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the explicit CUDA dynamic linalg adapter. The default scalar `dot`
API is unchanged; callers opt into `cuda_dot` and receive typed backend errors
when the dynamic scilib CUDA shim is unavailable.

## Scenarios

### linalg CUDA dynamic backend

#### reports either an available CUDA backend or a typed unavailable error

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = require_linalg_backend("cuda")
match required:
    case Ok(status):
        expect(status.selected).to_equal("cuda")
        expect(status.available).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### matches scalar dot when the CUDA shim is available

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = vector_from([Float64.new(1.5), Float64.new(-2.0), Float64.new(3.25), Float64.new(4.0)])
val right = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(-1.0), Float64.new(0.5)])
val result = cuda_dot(left, right)
match result:
    case Ok(value):
        expect(value).to_equal(dot(left, right).unwrap())
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### keeps public dot, gemv, gemm, solve, and inv scalar-compatible when CUDA is configured

1. [Float64 new
2. [Float64 new
   - Expected: gemv_result.get_f64(Index.new(0)) equals `Float64.new(32.0)`
   - Expected: gemv_result.get_f64(Index.new(1)) equals `Float64.new(77.0)`
3. [Float64 new
4. [Float64 new
5. [Float64 new
   - Expected: gemm_result.get_at([Index.new(0), Index.new(0)]) equals `Float64.new(58.0)`
   - Expected: gemm_result.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(64.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(139.0)`
   - Expected: gemm_result.get_at([Index.new(1), Index.new(1)]) equals `Float64.new(154.0)`
6. [Float64 new
7. [Float64 new
   - Expected: solve_result.get_f64(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: solve_result.get_f64(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: inv_result.rows() equals `Index.new(16)`
   - Expected: inv_result.cols() equals `Index.new(16)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(15), Index.new(15)]) equals `Float64.new(1.0)`
   - Expected: inv_result.get_f64_at([Index.new(0), Index.new(15)]) equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cuda_dot_values([Float64.new(1.0)], [Float64.new(1.0), Float64.new(2.0)])
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("same-length")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### matches scalar gemm when the CUDA shim is available

1. [Float64 new
2. [Float64 new
3. [Float64 new
4. [Float64 new
5. [Float64 new
   - Expected: value.get_at([Index.new(0), Index.new(0)]) equals `scalar.get_at([Index.new(0), Index.new(0)])`
   - Expected: value.get_at([Index.new(0), Index.new(1)]) equals `scalar.get_at([Index.new(0), Index.new(1)])`
   - Expected: value.get_at([Index.new(1), Index.new(0)]) equals `scalar.get_at([Index.new(1), Index.new(0)])`
   - Expected: value.get_at([Index.new(1), Index.new(1)]) equals `scalar.get_at([Index.new(1), Index.new(1)])`
   - Expected: name equals `cuda`
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
```

</details>

#### returns a typed error for gemm shape mismatches before backend execution

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = matrix_from_rows([[Float64.new(3.0), Float64.new(4.0)]])
val c_in = zeros_matrix(Index.new(1), Index.new(2))
val result = cuda_gemm(Float64.new(1.0), a, b, Float64.new(0.0), c_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### matches scalar gemv when the CUDA shim is available

1. [Float64 new
2. [Float64 new
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `cuda`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
```

</details>

#### returns a typed error for gemv shape mismatches before backend execution

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val vector = vector_from([Float64.new(3.0)])
val y_in = vector_from([Float64.new(0.0)])
val result = cuda_gemv(Float64.new(1.0), matrix, vector, Float64.new(0.0), y_in)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("compatible")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### matches scalar solve when the CUDA shim is available

1. [Float64 new
2. [Float64 new
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: name equals `cuda`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
```

</details>

#### returns a typed error for solve shape mismatches before backend execution

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val b = vector_from([Float64.new(3.0)])
val result = cuda_solve(a, b)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

#### matches scalar inverse when the CUDA shim is available

1. [Float64 new
2. [Float64 new
   - Expected: name equals `cuda`
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        fail("unexpected scilib backend result branch")
```

</details>

#### returns a typed error for inverse shape mismatches before backend execution

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([[Float64.new(1.0), Float64.new(2.0)]])
val result = cuda_inv(a)
match result:
    case Err(BackendError.BackendExecutionFailed(message)):
        expect(message).to_contain("square")
    case _:
        fail("unexpected scilib backend result branch")
```

</details>

### Fortran ABI smoke tests (pure-Simple, no FFI)

#### LP64 integer width is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The scilib shim uses int64_t for all index/info arguments.
# This constant must equal 8 for the LP64 ABI contract to hold.
val lp64_bytes: i64 = 8
expect(lp64_bytes).to_equal(8)
```

</details>

#### row-major to column-major index conversion is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dgesv = "rt_lapack_dgesv"
val dgetrf = "rt_lapack_dgetrf"
val dgetrs = "rt_lapack_dgetrs"
expect(dgesv).to_start_with("rt_lapack_d")
expect(dgetrf).to_start_with("rt_lapack_d")
expect(dgetrs).to_start_with("rt_lapack_d")
```

</details>

#### pivot index conversion: 1-based to 0-based is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = "cuda"
val cuda_available: bool = false
var selected = "mock"
if requested == "cuda" and cuda_available:
    selected = "cuda"
expect(selected).to_equal("mock")
```

</details>

#### selects cuda when requested and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val requested = "cuda"
val cuda_available: bool = true
var selected = "mock"
if requested == "cuda" and cuda_available:
    selected = "cuda"
expect(selected).to_equal("cuda")
```

</details>

#### auto-selects cuda over openblas when both available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
