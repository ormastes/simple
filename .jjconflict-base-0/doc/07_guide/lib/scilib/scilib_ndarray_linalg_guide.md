# Scientific Computing: std.ndarray and std.linalg

This guide covers the `std.ndarray` typed-array substrate and the `std.linalg`
linear algebra facade, including BLAS and LAPACK operations.

---

## 1. Overview

`std.ndarray` provides `NDArray<T>` — a typed, multi-dimensional array backed by
a flat row-major buffer. It is the shared substrate for `std.linalg`, `std.df`,
and `std.ml`.

`std.linalg` layers higher-level linear algebra on top: BLAS (dot products,
matrix multiply, norms, scaled updates) and LAPACK (linear solve, matrix
inverse, determinant).

All public APIs use typed wrappers (`Float64`, `Int64`, `Index`, `Shape`,
`DType`) — never raw primitive types at call boundaries.

---

## 2. Imports

```simple
use std.ndarray.*          # NDArray, Shape, Index, DType, Float64, Int64
use std.linalg.*           # BLAS/LAPACK facade: solve, gemm, axpy, dot, norm, ...
```

For direct access to provider traits or low-level BLAS bindings:

```simple
use std.common.science_math.blas.*           # BlasHandle, NormOrd, LinalgError
use std.common.science_math.blas_provider.*  # BlasProvider trait
use std.common.science_math.lapack.*         # LapackInfo, LinalgError (6 variants)
use std.common.science_math.lapack_provider.* # LapackProvider trait
use std.common.science_math.linalg.*         # mat_mul, dot, mat_zeros, mat_identity
use std.common.science_math.perf_sugar.*     # alloc_f64, alloc_i64, ...
```

---

## 3. NDArray Basics

### 3.1 Creation

**Filled arrays**

```simple
val a = zeros(Shape.new([Index.new(4)]))              # 1-D, length 4, all 0.0
val b = ones(Shape.new([Index.new(2), Index.new(3)])) # 2x3 matrix, all 1.0
val c = full(Shape.new([Index.new(3)]), Float64.new(2.5))  # fill value
val d = empty(Shape.new([Index.new(2), Index.new(2)])) # uninitialized
```

**Range and sequence**

```simple
val r = arange(Float64.new(0.0), Float64.new(4.0), Float64.new(1.0))  # [0,1,2,3]
val s = linspace(Float64.new(0.0), Float64.new(1.0), Index.new(3))    # [0.0, 0.5, 1.0]
```

**Identity matrix**

```simple
val I = eye(Index.new(3))   # 3x3 identity (Float64)
```

**From a sequence**

```simple
val v = array([Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)])
val w = array_i64([Int64.new(10), Int64.new(20), Int64.new(30)])
```

### 3.2 Shape and dtype

```simple
a.shape   # -> Shape.new([Index.new(4)])
a.len()   # -> Index.new(4)
a.dtype   # -> DType.F64  (or DType.I64)
```

### 3.3 Indexing

Flat 1-D index:

```simple
val v = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
v.get(Index.new(0))   # -> Float64.new(1.0)
```

Multi-dimensional index (row-major):

```simple
val m = zeros(Shape.new([Index.new(2), Index.new(3)]))
m.get_at([Index.new(1), Index.new(2)])  # row 1, col 2
```

For Float64 arrays, `get_f64` returns a typed scalar directly:

```simple
val x = solve(a_matrix, b_vec).unwrap()
x.get_f64(Index.new(0))   # -> Float64.new(...)
```

---

## 4. Vector and Matrix Operations

`std.common.science_math.linalg` provides a lower-level `Matrix` struct and
free functions for row-major matrix arithmetic.

```simple
use std.common.science_math.linalg.*

val z = mat_zeros(2, 3)            # 2x3 zero Matrix
val I = mat_identity(4)            # 4x4 identity Matrix
val m = mat_from(2, 3, data_buf)   # wrap flat [f64] buffer

val d = dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])  # -> 32.0

val c = mat_mul(a_mat, b_mat)   # Matrix multiply; rows/cols checked internally
```

`Matrix.get(row, col)` reads an element; `Matrix.size()` returns element count.

---

## 5. BLAS Operations

All Layer-C BLAS functions work on `[f64]` flat buffers and return `Result`.
Import: `use std.linalg.*`

### 5.1 axpy — scaled vector add

`y = alpha * x + y`

```simple
val x = [1.0, 2.0, 3.0]
val y = [4.0, 5.0, 6.0]
val result = blas_axpy_f64(2.0, x, y)  # -> Ok([6.0, 9.0, 12.0])
```

Requires `x.len() == y.len()`; returns `Err(BlasProviderError.DimensionMismatch)` otherwise.

### 5.2 dot — inner product

```simple
val d = blas_dot_f64([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])  # -> Ok(32.0)
```

### 5.3 scal — scale in place

```simple
val scaled = blas_scal_f64(3.0, [1.0, 2.0, 4.0])  # -> Ok([3.0, 6.0, 12.0])
```

### 5.4 nrm2 — Euclidean norm

```simple
val n = blas_nrm2_f64([3.0, 4.0])  # -> 5.0  (always unwrapped)
```

### 5.5 gemv — matrix-vector multiply

`y = alpha * A * x + beta * y`  where A is m×n.

```simple
val a  = [1.0, 2.0, 3.0, 4.0]  # 2x2 row-major
val x  = [1.0, 1.0]
val y0 = [0.0, 0.0]
val y  = blas_gemv_f64(1.0, a, 2, 2, x, 0.0, y0)
# y -> Ok([3.0, 7.0])
```

Signature: `blas_gemv_f64(alpha, a, m, n, x, beta, y)`

### 5.6 gemm — matrix-matrix multiply

`C = alpha * A * B + beta * C`  where A is m×k, B is k×n, C is m×n.

```simple
val a   = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]      # 2x3
val b   = [7.0, 8.0, 9.0, 10.0, 11.0, 12.0]    # 3x2
val c_in = [0.0, 0.0, 0.0, 0.0]                 # 2x2
val c = blas_gemm_f64(1.0, a, 2, 3, b, 2, 0.0, c_in)
# c -> Ok([58.0, 64.0, 139.0, 154.0])
```

Signature: `blas_gemm_f64(alpha, a, m, k, b, n, beta, c)`

**Operand-swap note (T-BLAS-13):** The internal Layer-B transposes operands to
satisfy Fortran column-major convention. Row-major callers always pass operands
in the natural (row-major) order shown above.

### 5.7 copy and swap

```simple
val copy = blas_copy_f64(x)                  # -> Ok([f64])
val sw   = blas_swap_f64(x, y)               # -> Ok(SwapResult { x, y })
```

---

## 6. LAPACK Operations

`use std.linalg.*`  (Layer C — no raw pivot or workspace visible to callers)

### 6.1 solve — linear system A * x = b

```simple
val a = eye_matrix(Index.new(3))
val b = vector_from([Float64.new(7.0), Float64.new(3.0), Float64.new(9.0)])
val result = solve(a, b)         # -> Result<NDArray<Float64>, LinalgError>
val x = result.unwrap()
x.get_f64(Index.new(0))         # -> Float64.new(7.0)
```

Returns `Err(LinalgError.Singular(info))` when A is singular,
`Err(LinalgError.DimensionMismatch)` on shape mismatch.

### 6.2 inv — matrix inverse

```simple
val inv_a = lapack_inv_f64(n, a_flat)  # -> Result<[f64], LinalgError>
```

Internally calls `gesv` once per identity column.

### 6.3 det — determinant

```simple
val d = lapack_det_f64(n, a_flat)  # -> Result<f64, LinalgError>
```

Implemented via LU factorization (`getrf`); product of diagonal entries times
pivot sign.

### 6.4 Error types

`LinalgError` has six variants:

| Variant | Payload | Meaning |
|---|---|---|
| `Singular` | `i64` (LAPACK info) | Matrix is singular |
| `BadArgument` | `i64` (arg index) | Invalid argument |
| `NotConverged` | `i64` (iteration count) | Iterative method stalled |
| `DimensionMismatch` | — | Shape incompatibility |
| `UnsupportedDType` | — | Unsupported element type |
| `WorkspaceError` | — | Backend absent or allocation failed |

---

## 7. Backend Selection

The backend is selected via the `SIMPLE_BLAS_BACKEND` environment variable.
Selection order (first available wins):

| Value | Provider | Notes |
|---|---|---|
| `mock` | `MockCpuBlasProvider` / `MockLapackProvider` | Always available; correct small-N arithmetic; no native deps |
| `scalar` | `CpuBlasProvider` / `CpuLapackProvider` | Pure-Simple scalar loops; no native deps |
| `openblas` | `OpenBlasProvider` | SFFI boundary via `rt_scilib_openblas_*_bits` shim |
| `lapacke` | `LapackeProvider` | SFFI LAPACKE boundary; returns `WorkspaceError` if lib absent |
| `cublas` | `CudaBlasProvider` | cuBLAS via `rt_scilib_cublas_*` shim; GPU device memory |

The test runner sets `SIMPLE_BLAS_BACKEND=mock` automatically for
`test/03_system/feature/scilib/` paths. Do not override it in test code.

To check the active backend at runtime:

```simple
val h = BlasHandle.create()
h.backend_name()    # -> "mock"
```

---

## 8. Performance Notes

### 8.1 Bulk buffer allocation (perf_sugar)

`use std.common.science_math.perf_sugar.*`

Instead of push-loop construction for large arrays, use the typed bulk
allocators (PERF-SUGAR-001). These call runtime externs that return a
pre-zeroed buffer in a single allocation:

```simple
val buf = alloc_f64(1024)  # zero-filled [f64] of length 1024
val ibuf = alloc_i64(256)  # zero-filled [i64] of length 256
```

Available helpers: `alloc_f64`, `alloc_f32`, `alloc_i64`, `alloc_i32`.

### 8.2 Thread safety

`BlasHandle` is a per-process singleton in v1. Do not cross actor boundaries
with a handle. Actor-aware per-fiber handles are planned for v1.1.

### 8.3 Generic variants

All BLAS and LAPACK operations are `Float64` (non-generic) in v1. Generic
`<T>` variants are deferred to v1.1 (PERF-SUGAR-003) pending interpreter
dispatch-erasure work.

### 8.4 Matrix layout

All flat buffers are **row-major**. The LAPACK SFFI layer converts to
column-major at the extern boundary using the operand-swap identity
`(AB)^T = B^T A^T` (OQ-C). Callers always work in row-major.
