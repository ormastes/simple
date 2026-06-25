# Fortran / CUDA ABI Research — scilib Port

**Date:** 2026-04-27
**Scope:** Fortran calling conventions, ISO_C_BINDING, cuBLAS/cuSOLVER C API, cuDF/cuML availability,
host-only fallback (OpenBLAS/Netlib), existing Simple FFI patterns, layering recommendation.

---

## 1. Fortran Calling Conventions

Classical Fortran (Fortran 77–90) has four ABI properties that differ from C:

| Property | Detail |
|---|---|
| Storage order | Column-major. Row `i`, col `j` of `m×n` lives at `(j-1)*m + (i-1)` (1-based) or `j*m + i` (0-based). |
| Index base | 1-based. cuBLAS carries this through (index results are 1-based). |
| Scalar arguments | Passed by reference. `DOUBLE PRECISION alpha` → `double *alpha` in C. |
| Name mangling | Compiler-dependent. gfortran/ifort/nvfortran: append one underscore, lower-cased (`dgemm_`). Double-underscore only when the name contains an internal underscore (`some_fn` → `some_fn__`). |
| String-length args | `CHARACTER` params cause hidden trailing `size_t` (gfortran ≥ GCC 8) or `int` (ifort) length args at the end of the C arg list. Every `UPLO`/`TRANS` flag character gets one. |

### ISO_C_BINDING vs cblas/lapacke

Fortran 2003 `ISO_C_BINDING` + `BIND(C)` produces clean C-callable symbols with no mangling and
value-mode scalars. In practice the BLAS/LAPACK ecosystem has converged on two C header interfaces
that completely bypass Fortran ABI hazards:

- **cblas.h** — ships with OpenBLAS, Netlib, MKL. `enum CBLAS_ORDER`/`CBLAS_TRANSPOSE` replace
  character flags; no hidden length args. E.g. `cblas_dgemm(CblasColMajor, CblasNoTrans, ...)`.
- **lapacke.h** — C interface to LAPACK (bundled with OpenBLAS ≥ 0.3). `LAPACKE_dgesv(LAPACK_COL_MAJOR, n, nrhs, a, lda, ipiv, b, ldb)`.

---

## 2. cuBLAS / cuSOLVER: Practical CUDA Route

NVIDIA provides cuBLAS and cuSOLVER as pure **C APIs**. No nvfortran compiler is required.

### 2.1 cuBLAS C API

Header: `cublas_v2.h` (current API, CUDA ≥ 6.0). Linked against `-lcublas`.

Key lifecycle:
```
cublasStatus_t cublasCreate(cublasHandle_t *handle)
cublasStatus_t cublasDestroy(cublasHandle_t handle)
```

Key data-transfer helpers (host ↔ device):
```
cublasSetMatrix(rows, cols, elemSize, A_host, lda_host, A_dev, lda_dev)
cublasGetMatrix(rows, cols, elemSize, A_dev,  lda_dev,  A_host, lda_host)
cublasSetMatrixAsync(..., stream)   // non-blocking variant
```

Compute example — DGEMM:
```
cublasStatus_t cublasDgemm(
    cublasHandle_t handle,
    cublasOperation_t transa, cublasOperation_t transb,
    int m, int n, int k,
    const double *alpha,          // host or device pointer
    const double *A, int lda,     // device pointer
    const double *B, int ldb,     // device pointer
    const double *beta,           // host or device pointer
    double *C, int ldc            // device pointer
)
```

**cuBLAS is always column-major, 1-based.** For a row-major NDArray the standard idiom is to
swap operands and use `CUBLAS_OP_T`: since `(AB)ᵀ = BᵀAᵀ`, calling
`cublasDgemm(..., B_row_ptr, A_row_ptr, ...)` with both ops set to `CUBLAS_OP_T` delivers
`AB` in row-major layout. This swap must be baked into Layer B (the SFFI wrapper) so the
public API (`linalg.gemm(a, b)`) is row-major throughout.

Error type: `cublasStatus_t` (enum `int`). All functions return it; the handle is first arg.

The cuBLAS 64-bit integer interface (`_64` suffix variants, CUDA ≥ 11.7) replaces `int` dims
with `int64_t`; this should be the binding target since Simple's `Index` wrapper will be 64-bit.

### 2.2 cuSOLVER C API

Header: `cusolverDn.h`. Linked against `-lcusolver`. Provides LAPACK-like factorizations on GPU
(LU, QR, SVD, Cholesky, eigenvalues, iterative-refinement gesv).

Key lifecycle:
```
cusolverStatus_t cusolverDnCreate(cusolverDnHandle_t *handle)
cusolverStatus_t cusolverDnDestroy(cusolverDnHandle_t handle)
```

Factorization pattern (LU, two-call: buffer query then compute):
```
cusolverDnDgetrf_bufferSize(handle, m, n, A, lda, &Lwork)  // query workspace
cusolverDnDgetrf(handle, m, n, A, lda, Workspace, devIpiv, devInfo)
cusolverDnDgetrs(handle, CUBLAS_OP_N, n, nrhs, A, lda, devIpiv, B, ldb, devInfo)
```

The new generic (`Xgetrf`/`Xgesv`) API uses `CUDA_R_64F` type descriptors and supports mixed
precision; it is the preferred binding target over the legacy `S`/`D`/`C`/`Z` prefixed functions.

---

## 3. cuDF and cuML: ABI Reality Check

| Library | Public ABI | Assessment |
|---|---|---|
| **libcudf** | C++ only. `cudf::column`, `cudf::table`, `cudf::io::*` are C++ classes; no `extern "C"` surface is guaranteed stable. | Writing Simple bindings requires a handwritten C-shim layer against an unstable C++ ABI. This is a significant engineering project, not a binding task. |
| **libcuml** | C++ primary. A partial C API exists (`cuml/cuml_api.h`) but covers only some algorithms and is not comprehensive. | Same issue: shim required for full coverage. |

**Recommendation: defer cuDF and cuML to v2.** Direct Simple `extern` declarations against an
unstable C++ ABI are fragile; defining `libspl_rapids.so` should wait until RAPIDS publishes a
stable `extern "C"` surface. For v1, tabular ops can be represented as NDArray slices.

---

## 4. Host-Only Fallback: OpenBLAS / Netlib LAPACK

For CI environments and no-GPU boxes, the fallback stack is:

| Library | Header | Link flag | pkg-config name | Notes |
|---|---|---|---|---|
| OpenBLAS | `cblas.h`, `lapacke.h` | `-lopenblas` | `openblas` | Ships cblas + lapacke in one lib since ≥ 0.3. Most distros provide `libopenblas-dev`. |
| Netlib CBLAS | `cblas.h` | `-lcblas -lblas` | `blas` / `cblas` | Reference; slower than OpenBLAS. |
| Netlib LAPACKE | `lapacke.h` | `-llapacke -llapack` | `lapack` / `lapacke` | Pure reference. |
| Apple Accelerate | `Accelerate/Accelerate.h` | `-framework Accelerate` | — | macOS only; cblas-compatible. |

dlopen strategy: the C-shim crate (see §5) should support both compile-time static linkage and
runtime `dlopen`, governed by a feature flag or environment variable (`SIMPLE_BLAS_BACKEND=cublas|openblas`).
The `RuntimeSymbolProvider` / `DynamicSymbolProvider` pattern already in
`src/compiler_rust/common/src/runtime_symbols.rs` provides the correct abstraction.

---

## 5. Existing Simple FFI Patterns

The codebase uses three FFI layers (from `src/lib/nogc_sync_mut/ffi/dynamic.spl` and
`src/compiler_rust/native_loader/src/static_provider.rs`):

1. **Raw `extern fn` decls** — primitive types only (`i64`/`f64`/ptr-as-`i64`). Convention: `rt_`
   prefix matching `#[no_mangle] pub extern "C" fn rt_*` in the Rust runtime or a C-shim `.so`.
2. **SFFI via `DynLib`** — `spl_dlopen`/`spl_dlsym`/`spl_wffi_call_i64`. `libspl_{prefix}.so`
   in `$SIMPLE_SFFI_PATH`. **Caveat:** `spl_dlopen` is not whitelisted in interpreter mode.
3. **`StaticSymbolProvider`** — zero-cost compiled-in function pointers for symbols baked into the
   seed binary.

The three-layer public API stack for BLAS (`std.linalg`):

| Layer | Location | Role |
|---|---|---|
| A — raw `extern fn` (primitives only) | `linalg/ffi_blas.spl` | `rt_blas_dgemm(handle:i64, m:i64, n:i64, k:i64, alpha:f64, a_ptr:i64, ...) -> i64` |
| B — SFFI wrapper (internal) | `linalg/blas.spl` | converts `Float64`/`NDArray<Float64>`/`Index` ↔ raw; applies operand-swap trick |
| C — public Simple API | `linalg/mod.spl` | `linalg.gemm(a: NDArray<Float64>, b: NDArray<Float64>) -> NDArray<Float64>` — no primitives visible |

The `libspl_torch.so` / `rt_torch_*` pattern is the direct template: replace `torch` → `cublas`
and `torch` → `lapack`.

---

## 6. Layering Recommendation: Thin C/Rust Shim vs Direct `extern`

**Recommendation: thin C/Rust shim crate exposing `rt_blas_*` / `rt_lapack_*` symbols,
dynamically loaded as `libspl_cublas.so` and `libspl_lapack.so`.**

| Option | Pros | Cons |
|---|---|---|
| **A. Thin shim (recommended)** | Isolates C type casting, handle lifecycle, workspace allocation; swap cuBLAS ↔ OpenBLAS by relinking the shim; mirrors `libspl_torch` pattern already in codebase | Extra `.so` artifact; cross-compile requires CUDA toolkit on build host |
| B. Direct Simple `extern fn` to cublas | No shim layer; fewer files | `cublasHandle_t` is an opaque struct pointer — must be carried as `i64`; workspace double-call pattern (bufferSize then compute) is awkward to express without helpers; no fallback switching |
| C. nvfortran direct | Uses Fortran-native interface | Name mangling per compiler (gfortran ≠ nvfortran); hidden string-length args for every `CHARACTER` parameter; no interpreter-mode path; strictly worse ergonomics |

The shim crate should expose: `rt_blas_handle_create`/`_destroy`; 64-bit-index variants only
(cuBLAS `_64` suffix); device-pointer args as opaque `i64`; companion `rt_cuda_malloc`,
`rt_cuda_free`, `rt_cuda_memcpy_htod`/`_dtoh`. When `SIMPLE_BLAS_BACKEND=openblas`, the same
`rt_blas_*` symbols resolve to cblas/lapacke host calls; device-pointer args become host pointers.

---

## 7. v1 Backend Recommendation

**v1 = cuBLAS + cuSOLVER C API via the thin shim crate, with OpenBLAS/Netlib as compile-time
fallback through the same `rt_blas_*` / `rt_lapack_*` symbol set.**

nvfortran-direct is rejected for v1: name mangling differs across nvfortran/gfortran/ifort,
string-length hidden args require per-compiler detection, and there is no interpreter-mode story.

cuDF and cuML are deferred to v2 pending a stable `extern "C"` API from RAPIDS.

---

## Open Questions

1. **Row-major vs column-major commitment.** The recommendation above uses the operand-swap
   trick (`(AB)ᵀ = BᵀAᵀ`) to present row-major NDArrays to cuBLAS. This must be decided before
   `NDArray` layout is finalised — changing it post-spec would touch every BLAS binding.

2. **Interpreter-mode spec execution (AC-7 conflict).** `spl_dlopen` is not whitelisted in
   interpreter mode, so cuBLAS specs cannot run fully interpreted. Options: (a) add `rt_blas_*`
   symbols to the Rust static provider (requires bootstrap rebuild per `feedback_extern_bootstrap_rebuild`);
   (b) run BLAS specs in compiled mode only and explicitly mark them with a `#[compiled_only]`
   annotation; (c) provide a mock/stub `libspl_cublas.so` with deterministic dummy returns for
   spec testing. Option (c) is preferable for CI portability and should be recorded as a
   feature request if stub generation is not already supported.

3. **cuBLAS 64-bit integer interface adoption.** The `_64` suffix API (`cublasDgemm_64`) is only
   available from CUDA 11.7+. If the project must support older CUDA (11.0–11.6), the 32-bit
   interface must remain as a fallback, requiring `Index` → `i32` clamping in Layer B.

4. **cuDF/cuML v2 scope.** Avoid coupling NDArray/DataFrame internals to libcudf C++ layout until
   RAPIDS publishes a stable `extern "C"` surface (github.com/rapidsai/cudf, rapidsai/cuml).

5. **SimpleOS / musl static targets.** `dlopen` is unavailable on SimpleOS. A vendored static
   OpenBLAS or `NotSupported` stub must be planned before `std.linalg` API is locked.

6. **Handle lifecycle and thread safety.** `cublasHandle_t` is per-thread (NVIDIA recommendation).
   Decide: global `BlasHandle` singleton or one per actor/fiber (interacts with `nogc_async_mut/`).
