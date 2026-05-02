# scilib-port BLAS TODO — `std.linalg` BLAS-Level Bindings

**Status:** Phase 4 (spec/TODO) — ready for Phase 5 impl  
**Area:** blas  
**Output path:** `src/lib/common/linalg/`  
**Import:** `use std.linalg`  
**Date:** 2026-04-27

---

## Scope

This file covers the **BLAS-level public API** for `std.linalg`:

- Operations: `axpy`, `scal`, `dot`, `norm` (L1/L2/Inf), `gemv`, `gemm`
- Each operation: Layer A extern decl → Layer B operand-swap shim → Layer C public API → spec
- Mock shim symbol stubs with correct small-N values (not zero-stubs)
- Handle lifecycle and thread-safety policy for `BlasHandle`
- PERF-SUGAR-003 workaround (non-generic specializations for interp mode)

**`scal` is included** — it appears in architect §13 BLAS dispatch scope (not §5 signature table, but explicitly in §13's `scilib_port_blas.md` scope line alongside axpy/nrm2).  
**`copy` is excluded** — not listed in §5 or §13.

**Scope disjoint from:**

| Sibling area | Boundary |
|---|---|
| `perf_sugar` | `rt_f64_array_alloc` extern + bootstrap rebuild — must be `fixed` before this area begins (hard gate T-PERF-001) |
| `ndarray` | `NDArray<T>`, `Matrix<T>`, `Vector<T>`, `Float64`, `Index`, `Shape`, `Stride` wrappers — consumed here, defined there (T-NDARRAY-03 through T-NDARRAY-07) |
| `lapack` | Layer A file `linalg/ffi_lapack.spl`; LAPACK ops (gesv, getrf, geqrf, syevd, gesvd) — parallel sibling, disjoint files |
| `cuda_fortran` | Builds `libspl_cublas.so` / `libspl_openblas.so` / `libspl_cublas_mock.so` — consumes BLAS symbol contract from Layer A; that area does the `.so` compilation |
| `math_block` | `@` token, `MatMul` AST, `math{}` interpreter extension — consumes `linalg.gemm`, does not define it |
| `df`, `ml`, `perf_sugar` | No overlap |

---

## Hard Constraints (enforce in every task)

1. **No primitive types in any public signature (Layer C).** `Float64`, `Matrix<Float64>`, `Vector<Float64>`, `Index`, `NormOrd` only. `f64`/`i64` are Layer A/B internal.
2. **Row-major external, column-major internal (OQ-C).** Layer B applies the operand-swap. Callers never see column-major.
3. **cuBLAS C API only (anti-pattern #1).** Layer A `extern fn` names cite cuBLAS C API symbols (`cublasDgemm_64`, `cublasDdot_64`, etc.), never Fortran mangled names (`dgemm_`, `ddot_`). This is a lint criterion on every Layer A decl.
4. **Mock backend for interp-mode (OQ-D / AC-7).** All specs must pass under `SIMPLE_BLAS_BACKEND=mock` in interpreter mode via `bin/simple test`. No `--mode=native` bypass (per `feedback_compile_mode_false_greens`). No `skip()`.
5. **PERF-SUGAR-001 hard gate.** Zero BLAS impl work begins until T-PERF-001 is `fixed`.
6. **No cover-ups (feedback_no_coverups).** If a spec cannot run in interp mode, file a compiler bug; do not add `skip()` or weaken assertions.

---

## Cross-Area Dependency Summary

| Dep ID | Source area | What is needed |
|---|---|---|
| T-PERF-001 | perf_sugar | `rt_f64_array_alloc` landed; bootstrap rebuild complete |
| T-NDARRAY-03 | ndarray | `Float64`, `Float32`, `Int64`, `Index` wrapper types defined |
| T-NDARRAY-04 | ndarray | `Shape`, `Stride` types defined |
| T-NDARRAY-05 | ndarray | `Matrix<T>` rank-2 wrapper defined |
| T-NDARRAY-06 | ndarray | `Vector<T>` rank-1 wrapper defined |
| T-NDARRAY-07 | ndarray | `StorageBackend` trait + `MockBackend` constructor available |
| T-NDARRAY-08 | ndarray | Contiguity guarantee: `Matrix.as_raw_ptr() -> i64` (contiguous row-major buffer) |
| T-CUDA-01 | cuda_fortran | `libspl_cublas.so` / `libspl_openblas.so` / `libspl_cublas_mock.so` built and placed in `$SIMPLE_SFFI_PATH` |

---

## Task List (topo-sorted, v1 first)

---

### T-BLAS-01 — Define `LinalgError`, `NormOrd`, and `BlasHandle` skeleton

**Effort:** ≤ 1 day  
**Depends on:** T-NDARRAY-03 (Index, DType)  
**Blocks:** T-BLAS-02 through T-BLAS-16  
**Files:** `src/lib/common/linalg/types.spl`

Define in `types.spl` (no primitives in public signatures):

- `enum NormOrd { L1, L2, Inf }` — used by `linalg.norm`.
- `enum LinalgError { Singular, NotConverged(iterations: Index), DimensionMismatch(expected: Shape, got: Shape), UnsupportedDType(dtype: DType) }` — shared with `lapack` area; coordinate on definition location.
- `struct BlasHandle { _handle_ptr: i64 }` — internal; `_handle_ptr` stores the raw `cublasHandle_t` cast to `i64`. Not exported in public API.
- `fn BlasHandle.create() -> Result<BlasHandle, LinalgError>` — calls `rt_blas_handle_create()` from Layer A (T-BLAS-02); selects backend per `SIMPLE_BLAS_BACKEND` env var.
- `fn BlasHandle.destroy(self)` — calls `rt_blas_handle_destroy()`.

**Thread-safety policy (lock here, reference everywhere):**  
`cublasHandle_t` is per-thread (NVIDIA recommendation). Policy for v1: one module-level `BlasHandle` singleton; interaction with `nogc_async_mut` actors is forbidden without explicit lock. Document this restriction as a `# THREAD-SAFETY` comment in `types.spl`. v1.1 will revisit once actor-aware handle-per-fiber is designed.

**Acceptance criteria:**
- `LinalgError`, `NormOrd`, `BlasHandle` compile in interpreter mode.
- No primitive type in any public signature.
- `# THREAD-SAFETY: one handle per process in v1; actor boundary crossing forbidden` comment present.

---

### T-BLAS-02 — Layer A: `extern fn` skeleton for handle lifecycle + BLAS level-1 ops

**Effort:** ≤ 1 day  
**Depends on:** T-BLAS-01, T-NDARRAY-03  
**Blocks:** T-BLAS-03, T-BLAS-05, T-BLAS-07, T-BLAS-09, T-BLAS-11  
**Files:** `src/lib/common/linalg/ffi_blas.spl`

Declare all Layer A `extern fn` signatures. Layer A is **primitive-only** (i64/f64): this is the correct layer for raw types. All names use `rt_blas_` prefix matching the symbol naming convention from architecture §6.

Curent required symbols (cite C API target in adjacent comment, never Fortran mangled name):

```
# handle lifecycle — cublas: cublasCreate / cublasDestroy
extern fn rt_blas_handle_create() -> i64
extern fn rt_blas_handle_destroy(handle: i64) -> i64

# BLAS level-1 — cuBLAS C API: cublasDaxpy_64 / cublasDscal_64 / cublasDdot_64 / cublasDnrm2_64 / cublasDasum_64 / cublasIdamax_64
extern fn rt_blas_daxpy(handle: i64, n: i64, alpha: f64, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64) -> i64
extern fn rt_blas_dscal(handle: i64, n: i64, alpha: f64, x_ptr: i64, incx: i64) -> i64
extern fn rt_blas_ddot(handle: i64, n: i64, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64, result_ptr: i64) -> i64
extern fn rt_blas_dnrm2(handle: i64, n: i64, x_ptr: i64, incx: i64, result_ptr: i64) -> i64
extern fn rt_blas_dasum(handle: i64, n: i64, x_ptr: i64, incx: i64, result_ptr: i64) -> i64
extern fn rt_blas_idamax(handle: i64, n: i64, x_ptr: i64, incx: i64, result_ptr: i64) -> i64

# BLAS level-2 — cublasDgemv_64
extern fn rt_blas_dgemv(handle: i64, trans: i64, m: i64, n: i64, alpha: f64, a_ptr: i64, lda: i64, x_ptr: i64, incx: i64, beta: f64, y_ptr: i64, incy: i64) -> i64

# BLAS level-3 — cublasDgemm_64
extern fn rt_blas_dgemm(handle: i64, transa: i64, transb: i64, m: i64, n: i64, k: i64, alpha: f64, a_ptr: i64, lda: i64, b_ptr: i64, ldb: i64, beta: f64, c_ptr: i64, ldc: i64) -> i64
```

**Lint criterion:** Every `extern fn` declaration must have an adjacent comment citing the exact cuBLAS C API function name it maps to (e.g., `# cublasDgemm_64`). This is a code-review gate — any `dgemm_` (Fortran mangled) in any comment is a violation of anti-pattern #1.

**Acceptance criteria:**
- File compiles (interpreter parses extern decls).
- Every decl has adjacent cuBLAS C API symbol citation in comment.
- No Fortran mangled names anywhere in file.

---

### T-BLAS-03 — Layer B: `axpy` SFFI wrapper with operand validation

**Effort:** ≤ 1 day  
**Depends on:** T-BLAS-02, T-NDARRAY-03, T-NDARRAY-06  
**Blocks:** T-BLAS-04 (Layer C axpy)  
**Files:** `src/lib/common/linalg/blas.spl`

Implement `blas_axpy_f64` in `blas.spl` (internal, not exported from `mod.spl`):

- Signature: `fn blas_axpy_f64(handle: BlasHandle, alpha: Float64, x: Vector<Float64>, y: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>`
- Unwrap `Float64._v` → `f64`, `Vector._inner` → `NDArray`, call `NDArray.as_raw_ptr()` → `i64`.
- Assert `x.len() == y.len()`; return `LinalgError.DimensionMismatch` on failure.
- Call `rt_blas_daxpy(handle._handle_ptr, n, alpha_f64, x_ptr, 1, y_ptr, 1)`.
- `axpy` is a level-1 operation (vector). **No operand-swap needed** — vectors have no layout orientation ambiguity. Document this explicitly to distinguish from gemm/gemv.
- Return `Result.Ok(y)` (axpy is in-place on y; return a view of y, not a copy).

**PERF-SUGAR-003 note:** `axpy` is generic in the long run but in v1 interp mode, provide `blas_axpy_f64` only (non-generic). A generic `axpy<T>` facade is added in T-BLAS-04 at Layer C, which will dispatch by `DType` at runtime. Mark with `# PERF-SUGAR-003: generic dispatch is erased in interp; specialization for F64 only in v1` comment.

**Acceptance criteria:**
- Unwrap/wrap at Layer B only; no primitives leak to Layer C callers.
- Dimension-mismatch returns `LinalgError.DimensionMismatch`, not a panic.
- Comment present: vectors require no operand-swap.

---

### T-BLAS-04 — Layer C: `linalg.axpy` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-03  
**Blocks:** T-BLAS-17 (axpy spec)  
**Files:** `src/lib/common/linalg/mod.spl`

Export from `mod.spl`:

```
fn axpy(alpha: Float64, x: Vector<Float64>, y: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>
```

Acquires the module-level `BlasHandle` singleton, delegates to `blas_axpy_f64`. No primitives in signature. DType guard: if `x._inner._dtype != DType.F64`, return `LinalgError.UnsupportedDType(x._inner._dtype)`.

**Acceptance criteria:**
- Public signature is fully no-primitive.
- `UnsupportedDType` returned for non-F64 input (tested in T-BLAS-17).

---

### T-BLAS-05 — Layer B: `scal` SFFI wrapper

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-02, T-NDARRAY-03, T-NDARRAY-06  
**Blocks:** T-BLAS-06 (Layer C scal)  
**Files:** `src/lib/common/linalg/blas.spl`

Implement `blas_scal_f64(handle, alpha: Float64, x: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>`.

- `dscal` scales `x` in-place: `x = alpha * x`. No second operand; no layout swap needed (vector).
- Calls `rt_blas_dscal(handle._handle_ptr, n, alpha_f64, x_ptr, 1)`.
- Returns `Result.Ok(x)` (in-place; same buffer).

**Acceptance criteria:** Same pattern as T-BLAS-03; no-primitive at boundary; in-place semantics documented.

---

### T-BLAS-06 — Layer C: `linalg.scal` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-05  
**Blocks:** T-BLAS-17 (scal spec)  
**Files:** `src/lib/common/linalg/mod.spl`

Export:
```
fn scal(alpha: Float64, x: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>
```

DType guard for non-F64. Document: `scal` mutates `x` in-place.

---

### T-BLAS-07 — Layer B: `dot` SFFI wrapper

**Effort:** ≤ 1 day  
**Depends on:** T-BLAS-02, T-NDARRAY-03, T-NDARRAY-06  
**Blocks:** T-BLAS-08 (Layer C dot)  
**Files:** `src/lib/common/linalg/blas.spl`

Implement `blas_dot_f64(handle, x: Vector<Float64>, y: Vector<Float64>) -> Result<Float64, LinalgError>`.

- `ddot` writes result into a host scalar. Layer B must allocate a one-element host buffer, pass its pointer to `rt_blas_ddot(..., result_ptr)`, then read back the result and wrap in `Float64`.
- Dimension check: `x.len() == y.len()`, else `LinalgError.DimensionMismatch`.
- No operand-swap needed (inner product is scalar, layout-invariant).

**PERF-SUGAR-003 note:** Non-generic `dot_f64` only in v1. Comment: `# PERF-SUGAR-003: dot_f64 is the v1 specialization; generic dot<T> added after monomorphization lands`.

**Acceptance criteria:**
- Result is `Float64` (no primitive leak).
- Dim-mismatch handled.
- Result buffer allocated and freed correctly (or managed by mock); no memory leak in spec run.

---

### T-BLAS-08 — Layer C: `linalg.dot` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-07  
**Blocks:** T-BLAS-17 (dot spec)  
**Files:** `src/lib/common/linalg/mod.spl`

Export:
```
fn dot(x: Vector<Float64>, y: Vector<Float64>) -> Result<Float64, LinalgError>
```

Return type is `Float64` (no-primitive rule; the wrapper is zero-cost once PERF-SUGAR-011 lands).

---

### T-BLAS-09 — Layer B: `norm` SFFI wrapper (three kernel dispatch)

**Effort:** ≤ 1.5 days  
**Depends on:** T-BLAS-01 (NormOrd), T-BLAS-02, T-NDARRAY-03, T-NDARRAY-06  
**Blocks:** T-BLAS-10 (Layer C norm)  
**Files:** `src/lib/common/linalg/blas.spl`

`norm` dispatches to **three different cuBLAS kernels** — this is not a single function. Each is a separate internal sub-function:

| `NormOrd` | cuBLAS kernel | Symbol | Notes |
|---|---|---|---|
| `L2` | `cublasDnrm2_64` | `rt_blas_dnrm2` | Euclidean norm; result written to scalar ptr |
| `L1` | `cublasDasum_64` | `rt_blas_dasum` | Sum of absolute values |
| `Inf` | `cublasIdamax_64` | `rt_blas_idamax` | Returns 1-based index of max abs element; Layer B reads `x[idx-1]` and takes absolute value to get the norm |

Implement:
- `blas_nrm2_f64(handle, x) -> Result<Float64, LinalgError>`
- `blas_asum_f64(handle, x) -> Result<Float64, LinalgError>`
- `blas_inf_norm_f64(handle, x) -> Result<Float64, LinalgError>` — calls `rt_blas_idamax`, converts 1-based result index to 0-based, reads element from x buffer, wraps `|x[idx]|` as `Float64`.

Public-facing `blas_norm_f64(handle, x, ord: NormOrd)` matches and delegates to the appropriate sub-function.

**Risk callout:** `idamax` result is 1-based (cuBLAS convention from Fortran ancestry). Layer B must subtract 1 before indexing into `x`. Forgetting this is a classic off-by-one. Add a `# cuBLAS convention: idamax result is 1-based; subtract 1 for 0-based index` comment and a spec assertion that catches it (T-BLAS-17 norm Inf test with known max at a non-zero index).

**Acceptance criteria:**
- Three sub-functions present; `blas_norm_f64` dispatches via `NormOrd` match.
- `idamax` 1-based → 0-based conversion documented and tested.
- All results wrapped in `Float64`.

---

### T-BLAS-10 — Layer C: `linalg.norm` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-09  
**Blocks:** T-BLAS-17 (norm spec)  
**Files:** `src/lib/common/linalg/mod.spl`

Export:
```
fn norm(x: NDArray<Float64>, ord: NormOrd) -> Result<Float64, LinalgError>
```

`x` may be any rank (vector or matrix treated as flattened for L1/L2/Inf norms). Dimension check: at least 1 element, else `LinalgError.DimensionMismatch`.

---

### T-BLAS-11 — Layer B: `gemv` SFFI wrapper with correct operand-swap (NOT gemm swap)

**Effort:** ≤ 1.5 days  
**Depends on:** T-BLAS-02, T-NDARRAY-03, T-NDARRAY-05, T-NDARRAY-06  
**Blocks:** T-BLAS-12 (Layer C gemv)  
**Files:** `src/lib/common/linalg/blas.spl`

Implement `blas_dgemv_f64(handle, alpha: Float64, a: Matrix<Float64>, x: Vector<Float64>, beta: Float64, y: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>`.

Computes: `y = alpha * A * x + beta * y`

**Critical — gemv operand-swap is different from gemm:** The `(AB)ᵀ = BᵀAᵀ` trick applies to matrix-matrix products only. For `gemv`:
- cuBLAS is column-major; our A is stored row-major.
- Row-major A is equivalent to column-major Aᵀ.
- So call `cublasDgemv_64` with `trans = CUBLAS_OP_T` and pass A's row-major buffer directly (no operand swap, just transpose flag).
- Vectors are layout-invariant: x and y are passed as-is.
- Document: `# gemv operand-swap: pass row-major A with CUBLAS_OP_T; do NOT use (AB)^T = B^T A^T (that is gemm only)`.

Dimension checks:
- A is `m×n`; x is length `n`; y is length `m`. Return `LinalgError.DimensionMismatch` if violated.

`trans` encoding in Layer A: `CUBLAS_OP_T = 1` (i64 constant, defined as named constant in `blas.spl`).

**Acceptance criteria:**
- `CUBLAS_OP_T` constant named (not magic number `1` inline).
- Comment distinguishing gemv transpose from gemm operand-swap present.
- Dimension checks present; tested in T-BLAS-18.

---

### T-BLAS-12 — Layer C: `linalg.gemv` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-11  
**Blocks:** T-BLAS-18 (gemv spec)  
**Files:** `src/lib/common/linalg/mod.spl`

Export (matches architecture §5):
```
fn gemv(alpha: Float64, a: Matrix<Float64>, x: Vector<Float64>, beta: Float64, y: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>
```

No primitives. DType guard for F64.

---

### T-BLAS-13 — Layer B: `gemm` SFFI wrapper with `(AB)ᵀ = BᵀAᵀ` operand-swap

**Effort:** ≤ 2 days  
**Depends on:** T-BLAS-02, T-NDARRAY-03, T-NDARRAY-05, T-NDARRAY-08  
**Blocks:** T-BLAS-14 (Layer C gemm)  
**Files:** `src/lib/common/linalg/blas.spl`

Implement `blas_dgemm_f64(handle, alpha: Float64, a: Matrix<Float64>, b: Matrix<Float64>, beta: Float64, c: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>`.

Computes: `C = alpha * A * B + beta * C`

**Operand-swap (OQ-C):** cuBLAS is column-major. For row-major A (m×k) and B (k×n):
- `(AB)ᵀ = BᵀAᵀ`
- Call `cublasDgemm_64(handle, CUBLAS_OP_T, CUBLAS_OP_T, n, m, k, alpha, B_ptr, ldb=n, A_ptr, lda=m, beta, C_ptr, ldc=n)`
- Note: m and n are **swapped** in the call (cuBLAS expects the leading dimension of the transposed output).
- Leading dimensions: `lda = k` (row stride of A), `ldb = n` (row stride of B), `ldc = n` (row stride of C).
- Result C is returned in row-major layout (no additional transpose needed).

Document with a detailed comment block explaining the swap. This is the most subtle transformation in the BLAS area and must be reviewable without access to cuBLAS documentation.

Dimension checks:
- A is `m×k`, B is `k×n`, C is `m×n`. All must match; `LinalgError.DimensionMismatch` otherwise.
- Both A and B must be contiguous (T-NDARRAY-08 guarantee). If a strided view is passed, Layer B must call `.contiguous()` to materialize a copy first.

**Acceptance criteria:**
- Operand-swap comment block present with explicit explanation of m/n swap in cublasDgemm_64 args.
- Leading dimension computation documented: `lda=k, ldb=n, ldc=n`.
- Strided-view contiguity guard present (`.contiguous()` call if needed).
- Dim mismatch checked for all three matrices.

---

### T-BLAS-14 — Layer C: `linalg.gemm` public API

**Effort:** ≤ 0.5 day  
**Depends on:** T-BLAS-13  
**Blocks:** T-BLAS-18 (gemm spec), math_block area (consumes this)  
**Files:** `src/lib/common/linalg/mod.spl`

Export (matches architecture §5):
```
fn gemm(alpha: Float64, a: Matrix<Float64>, b: Matrix<Float64>, beta: Float64, c: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>
```

No primitives. DType guard for F64.

---

### T-BLAS-15 — Mock shim symbol stubs with correct small-N values

**Effort:** ≤ 2 days  
**Depends on:** T-BLAS-02 (Layer A symbol names finalized)  
**Blocks:** T-BLAS-17, T-BLAS-18 (specs rely on mock)  
**Coordinate with:** T-CUDA-01 (cuda_fortran area builds and places the `.so`)  
**Files:** `src/runtime/scilib/mock_shim.c` (specification of what to implement; T-CUDA-01 does the build)

**This task defines the behavioral contract for `libspl_cublas_mock.so`.** Write this as a spec document for T-CUDA-01 to implement, since the `.so` build lives in the cuda_fortran area. The contract covers:

**No zero-stub fallback rule:** Mock compute functions must return **correct answers for small fixed inputs** (not zeros, not NaN). If a spec asserts `dot([1.0, 2.0], [3.0, 4.0]) == Float64(11.0)` and the mock returns zero, the spec passes trivially and verifies nothing (AC-7 violation). The mock must actually compute the result for small N.

Mock behavior contract:
- `rt_blas_handle_create()` → returns `i64(1)` (valid handle sentinel).
- `rt_blas_handle_destroy(handle)` → returns `i64(0)` (success).
- `rt_blas_daxpy(handle, n, alpha, x_ptr, incx, y_ptr, incy)` → reads `n` elements from `x_ptr`, computes `alpha*x[i] + y[i]` for each, writes to `y_ptr`. Returns `i64(0)`.
- `rt_blas_dscal(handle, n, alpha, x_ptr, incx)` → reads n elements, multiplies by alpha in-place. Returns `i64(0)`.
- `rt_blas_ddot(handle, n, x_ptr, incx, y_ptr, incy, result_ptr)` → computes sum of `x[i]*y[i]`, writes `f64` to `result_ptr`. Returns `i64(0)`.
- `rt_blas_dnrm2(handle, n, x_ptr, incx, result_ptr)` → computes `sqrt(sum(x[i]^2))`, writes to `result_ptr`. Returns `i64(0)`.
- `rt_blas_dasum(handle, n, x_ptr, incx, result_ptr)` → computes `sum(|x[i]|)`, writes to `result_ptr`. Returns `i64(0)`.
- `rt_blas_idamax(handle, n, x_ptr, incx, result_ptr)` → finds index of max abs element, writes **1-based** index (cuBLAS convention) to `result_ptr`. Returns `i64(0)`.
- `rt_blas_dgemv(handle, trans, m, n, alpha, a_ptr, lda, x_ptr, incx, beta, y_ptr, incy)` → computes `y = alpha * A * x + beta * y` for small m,n (plain C loops). Returns `i64(0)`.
- `rt_blas_dgemm(handle, transa, transb, m, n, k, alpha, a_ptr, lda, b_ptr, ldb, beta, c_ptr, ldc)` → computes `C = alpha * A * B + beta * C` for small m,n,k (plain C triple loop). Returns `i64(0)`.

All pointer args are `intptr_t` (cast from `i64`). The mock reads/writes host memory directly. No CUDA, no cuBLAS linkage.

**Acceptance criteria (checked by T-CUDA-01):**
- All symbols present; `nm libspl_cublas_mock.so | grep rt_blas` lists all 9 compute functions + 2 lifecycle functions.
- `dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])` returns `32.0` (not `0.0`).
- `idamax([-1.0, 5.0, 3.0])` returns `2` (1-based index of `5.0`).

---

### T-BLAS-16 — PERF-SUGAR-003 workaround: dtype-dispatch facades at Layer C

**Effort:** ≤ 1 day  
**Depends on:** T-BLAS-04, T-BLAS-06, T-BLAS-08, T-BLAS-10, T-BLAS-12, T-BLAS-14  
**Blocks:** none (quality task)  
**Files:** `src/lib/common/linalg/mod.spl`

In interpreter mode, generic `<T>` dispatch is erased/boxed (PERF-SUGAR-003, status: `anticipated`, P0). Until the compiler delivers monomorphization, generic facades calling into typed specializations would degrade interp performance. v1 strategy: all public functions are **non-generic** and typed as `Float64` at Layer C. Generic `<T>` variants are added in v1.1 once PERF-SUGAR-003 is `observed` with a concrete mitigation plan.

This task:
1. Audits all Layer C functions in `mod.spl` for any unintended `<T>` generics.
2. Confirms that `dot`, `axpy`, `scal`, `norm`, `gemv`, `gemm` are all non-generic `Float64` in v1.
3. Adds a `# PERF-SUGAR-003: generic <T> variants deferred to v1.1 (interp dispatch erasure)` comment at the top of `mod.spl`.
4. Adds a comment listing the planned `v1.1` generic signatures so the next engineer knows the intent: `# v1.1: fn dot<T>(x: Vector<T>, y: Vector<T>) -> Result<T, LinalgError>`.

**Acceptance criteria:**
- Zero `<T>` generics in any Layer C public function in v1.
- Comment block present.
- Perf-sugar tracking entry PERF-SUGAR-003 updated to `observed` with workaround documented.

---

### T-BLAS-17 — Specs: axpy, scal, dot, norm

**Effort:** ≤ 2 days  
**Depends on:** T-BLAS-04, T-BLAS-06, T-BLAS-08, T-BLAS-10, T-BLAS-15  
**Blocks:** T-BLAS-19 (spec sweep)  
**Files:** `src/lib/common/linalg/axpy_spec.spl`, `scal_spec.spl`, `dot_spec.spl`, `norm_spec.spl`

Each spec file runs under `SIMPLE_BLAS_BACKEND=mock` in interpreter mode. No `skip()`. No `--mode=native`.

**Per-spec coverage required:**

`axpy_spec.spl`:
- Happy path: `axpy(Float64(2.0), [1.0, 2.0], [3.0, 4.0])` → `[5.0, 8.0]`
- Dimension mismatch: `axpy(alpha, x[3], y[4])` → `LinalgError.DimensionMismatch`
- DType unsupported: pass `Vector<Int64>` → `LinalgError.UnsupportedDType`

`scal_spec.spl`:
- Happy path: `scal(Float64(3.0), [1.0, 2.0, 3.0])` → `[3.0, 6.0, 9.0]`
- Zero alpha: result is all zeros (not an error)
- DType guard

`dot_spec.spl`:
- Happy path: `dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])` → `Float64(32.0)`
- Dimension mismatch: `dot(x[2], y[3])` → error
- Orthogonal vectors: `dot([1.0, 0.0], [0.0, 1.0])` → `Float64(0.0)`

`norm_spec.spl`:
- L2: `norm([3.0, 4.0], NormOrd.L2)` → `Float64(5.0)`
- L1: `norm([1.0, -2.0, 3.0], NormOrd.L1)` → `Float64(6.0)`
- Inf: `norm([1.0, -5.0, 3.0], NormOrd.Inf)` → `Float64(5.0)` — must use index `1` (0-based) not `0`; this tests the 1-based idamax correction from T-BLAS-09
- Inf with max at index 0: `norm([7.0, 2.0, 1.0], NormOrd.Inf)` → `Float64(7.0)` — exercises index 1 (1-based) = index 0 (0-based)

**Acceptance criteria:**
- All four spec files pass `bin/simple test` with `SIMPLE_BLAS_BACKEND=mock`.
- Zero `skip()`. Zero TODO→NOTE conversions. Zero primitive type in any assertion value.
- Inf-norm tests cover the idamax 1-based off-by-one case explicitly.

---

### T-BLAS-18 — Specs: gemv and gemm

**Effort:** ≤ 2 days  
**Depends on:** T-BLAS-12, T-BLAS-14, T-BLAS-15  
**Blocks:** T-BLAS-19 (spec sweep)  
**Files:** `src/lib/common/linalg/gemv_spec.spl`, `gemm_spec.spl`

`gemv_spec.spl`:
- Happy path: 2×2 matrix, 2-vector input:
  - A = `[[1.0, 2.0], [3.0, 4.0]]`, x = `[1.0, 1.0]`, alpha=1, beta=0, y=`[0.0, 0.0]`
  - Expected: `[3.0, 7.0]`
- Non-square matrix: A is 3×2, x is length 2, y is length 3 — verifies dimension handling.
- Dimension mismatch: A is 2×3, x is length 2 (wrong) → `LinalgError.DimensionMismatch`.
- Non-zero beta: A=`[[1.0, 0.0], [0.0, 1.0]]` (identity), x=`[2.0, 3.0]`, alpha=1, beta=0.5, y=`[4.0, 6.0]` → `[4.0, 6.0]` (i.e., x + 0.5y = `[2.0+2.0, 3.0+3.0]` = `[4.0, 6.0]`).
- DType guard.

`gemm_spec.spl`:
- Identity: `gemm(1.0, I_2x2, B_2x2, 0.0, C_2x2)` → B
- Non-trivial 2×2: A=`[[1,2],[3,4]]`, B=`[[5,6],[7,8]]`, expected C=`[[19,22],[43,50]]`
- Non-square: A is 2×3, B is 3×4, C is 2×4 — verifies shape compatibility.
- Dimension mismatch: A is 2×3, B is 2×4 (k mismatch) → `LinalgError.DimensionMismatch`.
- beta accumulation: `gemm(1.0, A, B, 1.0, C)` where C is not zeros — verifies `alpha*A*B + beta*C`.
- DType guard.

**`#[gpu_only]` annotation:** Add a single `#[gpu_only]` commented-out spec block at the bottom of `gemm_spec.spl` that runs the same 2×2 case with `SIMPLE_BLAS_BACKEND=cublas` for CI GPU stage. This block is excluded from `bin/simple test`; it documents the GPU-stage test contract.

**Acceptance criteria:**
- Both files pass `bin/simple test` with mock backend.
- Non-trivial numerical assertions (not just `== Float64(0.0)`).
- `#[gpu_only]` block present in `gemm_spec.spl`.
- DType guards tested.

---

### T-BLAS-19 — Spec sweep: lint + interp compliance audit

**Effort:** ≤ 1 day  
**Depends on:** T-BLAS-17, T-BLAS-18  
**Blocks:** v1 → v1.1 gate (architecture §12)  
**Files:** all `linalg/*_spec.spl`, `linalg/mod.spl`, `linalg/blas.spl`, `linalg/ffi_blas.spl`

Run:
```
bin/simple build lint src/lib/common/linalg/
bin/simple test src/lib/common/linalg/ SIMPLE_BLAS_BACKEND=mock
```

Audit checklist:
- [ ] Zero `skip()` in any spec.
- [ ] Zero TODO→NOTE conversions.
- [ ] Zero primitive type (`f64`, `i64`, `i32`, `bool`) in any Layer C public signature.
- [ ] Zero Fortran mangled names (`dgemm_`, `daxpy_`, etc.) anywhere in `ffi_blas.spl`.
- [ ] Every Layer A `extern fn` has a cuBLAS C API symbol citation comment.
- [ ] PERF-SUGAR-003 workaround comment in `mod.spl`.
- [ ] Thread-safety policy comment in `types.spl`.
- [ ] gemv vs gemm operand-swap distinction comment in `blas.spl`.
- [ ] `idamax` 1-based → 0-based correction comment in `blas.spl`.

Promote perf-sugar entries:
- PERF-SUGAR-003: update status to `observed`; document workaround (non-generic v1 specializations).
- PERF-SUGAR-011: update status to `observed` if `Float64` wrapper construction causes measurable alloc overhead in gemm spec; add measurement note.

**Acceptance criteria:**
- All checklist items green.
- `bin/simple test src/lib/common/linalg/` exits 0 with `SIMPLE_BLAS_BACKEND=mock`.
- PERF-SUGAR-003 and PERF-SUGAR-011 status updated in `scilib_perf_sugar.md`.

---

## Dependency Graph (visual)

```
T-PERF-001 (perf_sugar area — hard gate)
    └─► T-NDARRAY-03..08 (ndarray area — wrappers)
            └─► T-BLAS-01 (types: LinalgError, NormOrd, BlasHandle)
                    └─► T-BLAS-02 (Layer A: extern fn decls)
                            ├─► T-BLAS-03 → T-BLAS-04  (axpy L-A/B/C)
                            ├─► T-BLAS-05 → T-BLAS-06  (scal L-A/B/C)
                            ├─► T-BLAS-07 → T-BLAS-08  (dot L-A/B/C)
                            ├─► T-BLAS-09 → T-BLAS-10  (norm L-A/B/C)
                            ├─► T-BLAS-11 → T-BLAS-12  (gemv L-A/B/C)
                            └─► T-BLAS-13 → T-BLAS-14  (gemm L-A/B/C)
                ├─► T-BLAS-15  (mock shim contract — also needs T-CUDA-01)
                ├─► T-BLAS-16  (PERF-SUGAR-003 audit — after all Layer C)
                ├─► T-BLAS-17  (axpy/scal/dot/norm specs — needs T-BLAS-15)
                ├─► T-BLAS-18  (gemv/gemm specs — needs T-BLAS-15)
                └─► T-BLAS-19  (spec sweep — after T-BLAS-17+18)
```

Parallel-safe with `lapack` area: `ffi_blas.spl` vs `ffi_lapack.spl` are disjoint files. Do not edit `ffi_lapack.spl` from this area.

---

## Anti-Patterns (do not propose in impl or PR reviews)

1. **No nvfortran / Fortran mangled names.** Layer A calls cuBLAS C API (`cublasDgemm_64`), never `dgemm_`.
2. **No `--mode=native` or `--mode=smf` to bypass interp.** Both give false greens (`feedback_compile_mode_false_greens`). All specs via `bin/simple test`.
3. **No zero-stub mock.** Mock shim must compute correct small-N answers; zero-return stubs render AC-7 specs meaningless.
4. **No `skip()` or TODO→NOTE.** Per `feedback_no_coverups` and AC-7.
5. **No DataFrame ops in this area.** BLAS area is pure linalg; no `df.*` imports.
6. **No copy-paste of gemm operand-swap into gemv.** Different transforms; document difference explicitly.

---

## v1 Acceptance Gate Checklist (contributes to arch §12 v1→v1.1)

- [ ] `bin/simple test src/lib/common/linalg/` passes; zero `skip()` with `SIMPLE_BLAS_BACKEND=mock`.
- [ ] `linalg.axpy`, `linalg.scal`, `linalg.dot`, `linalg.norm`, `linalg.gemv`, `linalg.gemm` Layer C APIs public in `mod.spl`.
- [ ] Zero primitive type in any public Layer C signature (audited in T-BLAS-19).
- [ ] Zero Fortran mangled names in `ffi_blas.spl` (audited in T-BLAS-19).
- [ ] Mock shim behavioral contract (T-BLAS-15) delivered to cuda_fortran area (T-CUDA-01).
- [ ] PERF-SUGAR-003 workaround documented; status updated to `observed`.
- [ ] `BlasHandle` thread-safety policy documented in `types.spl`.
- [ ] gemv vs gemm operand-swap distinction documented in `blas.spl`.
- [ ] `idamax` 1-based off-by-one conversion documented and covered by a norm-Inf test with non-zero max index.
