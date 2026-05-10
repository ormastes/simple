# Agent Task File: scilib_port_cuda_fortran

**Area:** cuda_fortran — FFI shim crates for `libspl_cublas.so`, `libspl_openblas.so`, `libspl_cublas_mock.so`
**Owner phase:** Phase 5 sub-agent (cuda_fortran track)
**Status:** Ready (depends on blas + lapack task files completing symbol list)
**Date drafted:** 2026-04-27

---

## Scope and Disjointness

This file covers exclusively the **native C shim layer** that exposes the `rt_blas_*` and
`rt_lapack_*` symbol set to the Simple runtime.  It does NOT cover:

- Simple-side Layer A `extern fn` declarations (`ffi_blas.spl`, `ffi_lapack.spl`) — owned by
  `scilib_port_blas.md` and `scilib_port_lapack.md`
- Layer B SFFI wrappers (`blas.spl`, `lapack.spl`) — owned by the same two files
- Layer C public API (`linalg/mod.spl`) — owned by `scilib_port_blas.md`
- `NDArray<T>` and `StorageBackend` trait — owned by `scilib_port_ndarray.md`
- math-block compiler changes — owned by `scilib_port_math_block.md`
- df / ml / perf_sugar areas

Cross-area dependency: this task file **consumes** the final symbol list from `scilib_port_blas.md`
and `scilib_port_lapack.md` before T-CUDA-01 can be closed.  All three shim libraries must
implement **the identical symbol set**; any symbol added in blas/lapack tasks must be added to all
three shims in the same commit batch.

**Anti-patterns enforced throughout:**
1. No nvfortran toolchain — cuBLAS/cuSOLVER C API only (`cublas_v2.h`, `cusolverDn.h`).
3. No `--mode=native` to bypass mock — all specs run interpreter mode with `SIMPLE_BLAS_BACKEND=mock`.

---

## Architecture Reference

- Shim source location pattern: mirrors `src/runtime/torch_ffi.cpp` and `src/runtime/torch_ffi.h`
  (exact directory: `src/runtime/`).  Scilib shims live in `src/runtime/scilib/`.
- Three shim files:
  - `src/runtime/scilib/cublas_shim.c` — cuBLAS + cuSOLVER backend
  - `src/runtime/scilib/openblas_shim.c` — OpenBLAS/LAPACKE host backend
  - `src/runtime/scilib/mock_shim.c` — deterministic CPU stubs (OQ-D, interp-mode AC-7)
- Build output: `build/libspl_cublas.so`, `build/libspl_openblas.so`, `build/libspl_cublas_mock.so`
- `SIMPLE_SFFI_PATH` must contain all three `.so` files; mock is the default for `bin/simple test`.
- Backend selection: env var `SIMPLE_BLAS_BACKEND` (values: `cublas` | `openblas` | `mock`);
  when unset, dispatch order is cublas → openblas → mock.

---

## Symbol Convention (authoritative)

All exported symbols follow this naming scheme and must appear in all three shim libraries:

### Handle lifecycle
```
rt_blas_handle_create() -> i64          # returns opaque handle as i64; mock returns 1
rt_blas_handle_destroy(handle: i64)
rt_lapack_handle_create() -> i64        # cusolverDnCreate; mock returns 1
rt_lapack_handle_destroy(handle: i64)
rt_cuda_api_version() -> i64            # CUDA runtime version * 1000; mock returns 0
```

### CUDA memory management
```
rt_cuda_malloc(bytes: i64) -> i64       # device alloc; openblas/mock: host malloc
rt_cuda_free(ptr: i64)
rt_cuda_memcpy_htod(dst: i64, src: i64, bytes: i64)   # host-to-device
rt_cuda_memcpy_dtoh(dst: i64, src: i64, bytes: i64)   # device-to-host
rt_cuda_memcpy_dtod(dst: i64, src: i64, bytes: i64)   # device-to-device; mock: memcpy
```

### BLAS level-1 (double precision)
```
rt_blas_daxpy(handle: i64, n: i64, alpha: f64, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64)
rt_blas_ddot(handle: i64, n: i64, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64) -> f64
rt_blas_dnrm2(handle: i64, n: i64, x_ptr: i64, incx: i64) -> f64
rt_blas_dscal(handle: i64, n: i64, alpha: f64, x_ptr: i64, incx: i64)
```

### BLAS level-1 (single precision)
```
rt_blas_saxpy(handle: i64, n: i64, alpha: f32, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64)
rt_blas_sdot(handle: i64, n: i64, x_ptr: i64, incx: i64, y_ptr: i64, incy: i64) -> f32
rt_blas_snrm2(handle: i64, n: i64, x_ptr: i64, incx: i64) -> f32
rt_blas_sscal(handle: i64, n: i64, alpha: f32, x_ptr: i64, incx: i64)
```

### BLAS level-2
```
rt_blas_dgemv(handle: i64, trans: i64, m: i64, n: i64, alpha: f64,
              a_ptr: i64, lda: i64, x_ptr: i64, incx: i64,
              beta: f64, y_ptr: i64, incy: i64)
```

### BLAS level-3
```
rt_blas_dgemm(handle: i64, transa: i64, transb: i64,
              m: i64, n: i64, k: i64, alpha: f64,
              a_ptr: i64, lda: i64, b_ptr: i64, ldb: i64,
              beta: f64, c_ptr: i64, ldc: i64) -> i64   # returns status
rt_blas_sgemm(handle: i64, transa: i64, transb: i64,
              m: i64, n: i64, k: i64, alpha: f32,
              a_ptr: i64, lda: i64, b_ptr: i64, ldb: i64,
              beta: f32, c_ptr: i64, ldc: i64) -> i64
```

### LAPACK (cuSOLVER on CUDA; LAPACKE on OpenBLAS; CPU stubs on mock)
```
rt_lapack_dgesv(handle: i64, n: i64, nrhs: i64,
                a_ptr: i64, lda: i64, ipiv_ptr: i64,
                b_ptr: i64, ldb: i64) -> i64          # returns devInfo
rt_lapack_dgetrf(handle: i64, m: i64, n: i64,
                 a_ptr: i64, lda: i64, ipiv_ptr: i64) -> i64
rt_lapack_dgetri(handle: i64, n: i64,
                 a_ptr: i64, lda: i64, ipiv_ptr: i64,
                 work_ptr: i64, lwork: i64) -> i64
rt_lapack_dgetrf_bufsize(handle: i64, m: i64, n: i64,
                          a_ptr: i64, lda: i64) -> i64   # workspace bytes query
rt_lapack_dgeqrf(handle: i64, m: i64, n: i64,
                 a_ptr: i64, lda: i64, tau_ptr: i64,
                 work_ptr: i64, lwork: i64) -> i64
rt_lapack_dgeqrf_bufsize(handle: i64, m: i64, n: i64,
                          a_ptr: i64, lda: i64) -> i64
rt_lapack_dsyevd(handle: i64, jobz: i64, uplo: i64, n: i64,
                 a_ptr: i64, lda: i64, w_ptr: i64,
                 work_ptr: i64, lwork: i64,
                 iwork_ptr: i64, liwork: i64) -> i64
rt_lapack_dsyevd_bufsize(handle: i64, jobz: i64, uplo: i64, n: i64,
                          a_ptr: i64, lda: i64) -> i64    # returns (lwork, liwork) packed
rt_lapack_dgesvd(handle: i64, jobu: i64, jobvt: i64, m: i64, n: i64,
                 a_ptr: i64, lda: i64, s_ptr: i64,
                 u_ptr: i64, ldu: i64, vt_ptr: i64, ldvt: i64,
                 work_ptr: i64, lwork: i64) -> i64
rt_lapack_dgesvd_bufsize(handle: i64, jobu: i64, jobvt: i64, m: i64, n: i64) -> i64
```

---

## Dependency Order

```
T-CUDA-01  # crate scaffolding (no external dep)
    ↓
T-CUDA-02  # mock shim — enables all interp-mode specs immediately
    ↓
T-CUDA-03  # OpenBLAS shim — host-fallback CI
T-CUDA-04  # CUDA build detection (parallel with T-CUDA-03)
    ↓
T-CUDA-05  # cuBLAS shim (depends on T-CUDA-04)
    ↓
T-CUDA-06  # cuSOLVER shim (depends on T-CUDA-05)
    ↓
T-CUDA-07  # backend dispatch (depends on T-CUDA-02/03/05)
    ↓
T-CUDA-08  # Cargo.toml feature flags and workspace wiring
T-CUDA-09  # SFFI_PATH + test harness mock default (parallel with T-CUDA-08)
    ↓
T-CUDA-10  # scripts/setup.sh integration
T-CUDA-11  # bootstrap script wiring (parallel with T-CUDA-10)
    ↓
T-CUDA-12  # CI matrix (mock-only, openblas-host, cuda-host)
    ↓
T-CUDA-13  # smoke spec: all 3 backends pass rt_blas_dgemm identity check
T-CUDA-14  # symbol completeness verification vs blas+lapack task files
```

---

## Tasks

---

### T-CUDA-01: Scaffold `src/runtime/scilib/` directory and C shim stubs

**Estimate:** 0.5 day
**Depends on:** blas+lapack task files (symbol list must be frozen before this closes)
**Disjoint files:** `src/runtime/scilib/` (new directory — no conflict with torch or other areas)

Create the directory `src/runtime/scilib/` mirroring `src/runtime/torch_ffi.cpp` +
`src/runtime/torch_ffi.h` as the template.  Produce three empty C source files:

- `src/runtime/scilib/cublas_shim.c`
- `src/runtime/scilib/openblas_shim.c`
- `src/runtime/scilib/mock_shim.c`
- `src/runtime/scilib/scilib_shim.h` — shared header: all `rt_blas_*` / `rt_lapack_*`
  / `rt_cuda_*` function prototypes, one per line, with `__attribute__((visibility("default")))`.

Each `.c` file starts with a `#include "scilib_shim.h"` and a stub body `{ return 0; }` for every
symbol.  This compiles cleanly before any real implementation, establishing the build baseline.

**Done when:** `gcc -shared -fPIC src/runtime/scilib/mock_shim.c -o /tmp/test_mock.so` succeeds
with no warnings.

---

### T-CUDA-02: Implement `mock_shim.c` — deterministic CPU stubs for all symbols

**Estimate:** 1 day
**Depends on:** T-CUDA-01
**Disjoint files:** `src/runtime/scilib/mock_shim.c` only

Implement every symbol in `mock_shim.c` with a computable-on-CPU stub that:

- `rt_blas_handle_create` → returns `(int64_t)1`
- `rt_lapack_handle_create` → returns `(int64_t)1`
- `rt_cuda_api_version` → returns `(int64_t)0`
- `rt_cuda_malloc(bytes)` → `(int64_t)(uintptr_t)malloc(bytes)`
- `rt_cuda_free(ptr)` → `free((void*)(uintptr_t)ptr)`
- `rt_cuda_memcpy_htod(dst, src, bytes)` → `memcpy(...)` (host-to-host)
- `rt_cuda_memcpy_dtoh(dst, src, bytes)` → `memcpy(...)`
- `rt_cuda_memcpy_dtod(dst, src, bytes)` → `memcpy(...)`
- `rt_blas_dgemm(...)` → writes all-zeros to `c_ptr`; returns `0` (success status)
- `rt_blas_sgemm(...)` → writes all-zeros to `c_ptr`; returns `0`
- `rt_blas_dgemv(...)` → writes all-zeros to `y_ptr`
- `rt_blas_daxpy(...)` → copies `x` into `y` scaled by `alpha` (pure C loop, no BLAS)
- `rt_blas_ddot(...)` → returns `0.0`
- `rt_blas_dnrm2(...)` → returns `0.0`
- `rt_blas_dscal(...)` → scales in-place (pure C loop)
- `rt_blas_saxpy/sdot/snrm2/sscal` → float equivalents of above
- `rt_lapack_dgesv(...)` → fills `b_ptr` with zeros; `devInfo = 0`
- `rt_lapack_dgetrf(...)` → fills `a_ptr` with identity lower-triangle; `devInfo = 0`
- `rt_lapack_dgetri(...)` → no-op; `devInfo = 0`
- `rt_lapack_dgetrf_bufsize(...)` → returns `8192` (safe workspace estimate)
- `rt_lapack_dgeqrf(...)` → `devInfo = 0`; fills `tau_ptr` with zeros
- `rt_lapack_dgeqrf_bufsize(...)` → returns `8192`
- `rt_lapack_dsyevd(...)` → `devInfo = 0`; fills `w_ptr` with zeros
- `rt_lapack_dsyevd_bufsize(...)` → returns packed `(lwork=8192, liwork=128)` as `lwork | (liwork << 32)`
- `rt_lapack_dgesvd(...)` → `devInfo = 0`; fills `s_ptr` with zeros
- `rt_lapack_dgesvd_bufsize(...)` → returns `8192`

**Rationale (OQ-D):** The mock shim satisfies AC-7 — all `std.linalg` / `std.ndarray` specs run
under interpreter mode with `SIMPLE_BLAS_BACKEND=mock`.  Returning zeros / identity stubs is
sufficient for spec assertions that check shape, non-error return, and type correctness.  Specs
requiring numerically correct results are annotated `#[gpu_only]` and excluded from interpreter run.

**Done when:** `libspl_cublas_mock.so` compiles; `nm -D` shows all `rt_blas_*` / `rt_lapack_*` /
`rt_cuda_*` symbols as `T` (text, exported).

---

### T-CUDA-03: Implement `openblas_shim.c` — OpenBLAS/LAPACKE host backend

**Estimate:** 1.5 days
**Depends on:** T-CUDA-01
**Disjoint files:** `src/runtime/scilib/openblas_shim.c` only

Wire each `rt_blas_*` / `rt_lapack_*` symbol to the corresponding `cblas_` / `LAPACKE_` call:

- Include `<cblas.h>` and `<lapacke.h>` (detected via pkg-config `openblas` or
  `cblas` + `lapacke` separately).
- `rt_blas_handle_create` → returns `(int64_t)1` (no OpenBLAS handle needed)
- `rt_blas_dgemm(handle, transa, transb, m, n, k, alpha, a_ptr, lda, b_ptr, ldb, beta, c_ptr, ldc)`:
  - Maps `transa`/`transb` `i64` flags: `0 = CblasNoTrans`, `1 = CblasTrans`, `2 = CblasConjTrans`.
  - Calls `cblas_dgemm(CblasRowMajor, transa_e, transb_e, m, n, k, alpha, A, lda, B, ldb, beta, C, ldc)`.
  - **Note:** cuBLAS always takes column-major; operand-swap is done in Layer B (Simple side).  The
    openblas shim receives the already-swapped operands and calls with `CblasRowMajor`.  The shim
    must NOT apply any additional swap — that would double-swap.  Document this clearly.
- `rt_blas_dgemv` → `cblas_dgemv(CblasRowMajor, ...)`
- `rt_blas_daxpy` → `cblas_daxpy(...)`
- `rt_blas_ddot` → `cblas_ddot(...)`
- `rt_blas_dnrm2` → `cblas_dnrm2(...)`
- `rt_blas_dscal` → `cblas_dscal(...)`
- Equivalent single-precision wrappers (`sgemm`, `saxpy`, etc.)
- `rt_lapack_dgesv` → `LAPACKE_dgesv(LAPACK_ROW_MAJOR, n, nrhs, A, lda, ipiv, B, ldb)`
- `rt_lapack_dgetrf` → `LAPACKE_dgetrf(LAPACK_ROW_MAJOR, m, n, A, lda, ipiv)`
- `rt_lapack_dgetri` → `LAPACKE_dgetri(LAPACK_ROW_MAJOR, n, A, lda, ipiv)`
  - `work_ptr` / `lwork` args passed in from Layer B; if `lwork == -1`, call with lwork=-1 first
    to query (this is the bufsize path, but LAPACKE hides it internally — pass `lwork` directly
    and let LAPACKE manage workspace).
- `rt_lapack_dgetrf_bufsize` → returns `0` (LAPACKE manages workspace internally; Layer B should
  skip workspace allocation for the openblas path).
- `rt_lapack_dgeqrf` → `LAPACKE_dgeqrf(LAPACK_ROW_MAJOR, m, n, A, lda, tau)`
- `rt_lapack_dgeqrf_bufsize` → returns `0`
- `rt_lapack_dsyevd` → `LAPACKE_dsyevd(LAPACK_ROW_MAJOR, jobz_c, uplo_c, n, A, lda, w)`
  - Map `jobz: i64` → `'V'`/`'N'`; `uplo: i64` → `'U'`/`'L'`.
- `rt_lapack_dsyevd_bufsize` → returns packed `0 | (0 << 32)` (LAPACKE manages workspace)
- `rt_lapack_dgesvd` → `LAPACKE_dgesvd(LAPACK_ROW_MAJOR, jobu_c, jobvt_c, m, n, A, lda, s, U, ldu, Vt, ldvt, superb)`
  - Allocate a `superb[min(m,n)-1]` array on the stack for the superdiagonal.
- `rt_lapack_dgesvd_bufsize` → returns `0`
- `rt_cuda_malloc` → `malloc`; `rt_cuda_free` → `free`; memcpy variants → `memcpy`
- `rt_cuda_api_version` → `0`

**Static vs dynamic link option:** Controlled by `SIMPLE_OPENBLAS_STATIC=1` env var at build time.
When set, link `-Wl,-Bstatic -lopenblas -Wl,-Bdynamic`; otherwise dynamic `-lopenblas`.

**pkg-config detection:** CMakeLists.txt (or makefile fragment) calls
`pkg-config --cflags --libs openblas`; if not found, falls back to
`pkg-config --cflags --libs cblas lapacke`.  If neither found, the openblas shim build is
skipped and `build/libspl_openblas.so` is not produced (CI matrix detects this).

**Done when:** `nm -D build/libspl_openblas.so` shows all `rt_*` symbols; a minimal C test binary
linking the shim and calling `rt_blas_dgemm` for a 2×2 identity matrix returns correct result.

---

### T-CUDA-04: Detect CUDA toolkit at build time

**Estimate:** 0.5 day
**Depends on:** T-CUDA-01
**Disjoint files:** `src/runtime/scilib/CMakeLists.txt` (or `build_scilib.sh`)

Write a build detection script (CMakeLists.txt fragment or shell) that:

1. Checks for `nvcc` in `PATH` or `CUDA_PATH`/`CUDA_HOME` env vars.
2. Verifies `cublas_v2.h` and `cusolverDn.h` exist under the detected CUDA include path.
3. Verifies CUDA version ≥ 11.7 (required for `_64` integer interface).
   - If CUDA version is 11.0–11.6: emit a warning `CUDA <11.7 detected: using 32-bit index interface
     (Index→i32 clamping active in Layer B)` and set a build define `SIMPLE_CUDA_NO_64BIT=1`.
   - If CUDA < 11.0: fail with an error — not supported.
4. Sets CMake variables `CUDA_INCLUDE_DIR`, `CUBLAS_LIB`, `CUSOLVER_LIB`.
5. If CUDA not found: sets `SIMPLE_CUDA_AVAILABLE=0`; cublas_shim build is skipped.

Output: a generated header `src/runtime/scilib/cuda_version.h` with:
```c
#define SIMPLE_CUDA_MAJOR <N>
#define SIMPLE_CUDA_MINOR <N>
#define SIMPLE_CUDA_USE_64BIT  // omitted if CUDA < 11.7
```

**Done when:** Running the detection script on a GPU machine produces correct `cuda_version.h`;
running on a CPU-only machine sets `SIMPLE_CUDA_AVAILABLE=0` cleanly.

---

### T-CUDA-05: Implement `cublas_shim.c` — cuBLAS backend

**Estimate:** 1.5 days
**Depends on:** T-CUDA-04
**Disjoint files:** `src/runtime/scilib/cublas_shim.c` only

Implement all `rt_blas_*` and `rt_cuda_*` symbols against `cublas_v2.h`:

- `rt_blas_handle_create` → `cublasCreate(&h); return (int64_t)(uintptr_t)h`
- `rt_blas_handle_destroy(handle)` → `cublasDestroy((cublasHandle_t)(uintptr_t)handle)`
- `rt_cuda_api_version` → `cudaRuntimeGetVersion(&v); return (int64_t)v`
- `rt_cuda_malloc(bytes)` → `cudaMalloc(&ptr, bytes); return (int64_t)(uintptr_t)ptr`
- `rt_cuda_free(ptr)` → `cudaFree((void*)(uintptr_t)ptr)`
- `rt_cuda_memcpy_htod(dst, src, bytes)` → `cudaMemcpy(..., cudaMemcpyHostToDevice)`
- `rt_cuda_memcpy_dtoh(dst, src, bytes)` → `cudaMemcpy(..., cudaMemcpyDeviceToHost)`
- `rt_cuda_memcpy_dtod(dst, src, bytes)` → `cudaMemcpy(..., cudaMemcpyDeviceToDevice)`

For BLAS operations, use the `_64` suffix API when `SIMPLE_CUDA_USE_64BIT` is defined, else
fall back to 32-bit with `i32` clamping and an assertion:

```c
#ifdef SIMPLE_CUDA_USE_64BIT
  cublasDgemm_64(h, transa, transb, (int64_t)m, (int64_t)n, (int64_t)k,
                 &alpha, A, (int64_t)lda, B, (int64_t)ldb, &beta, C, (int64_t)ldc)
#else
  assert(m <= INT32_MAX && n <= INT32_MAX && k <= INT32_MAX);
  cublasDgemm(h, transa, transb, (int)m, (int)n, (int)k,
              &alpha, A, (int)lda, B, (int)ldb, &beta, C, (int)ldc)
#endif
```

Map operation flags: `transa`/`transb` as `i64`: `0 = CUBLAS_OP_N`, `1 = CUBLAS_OP_T`,
`2 = CUBLAS_OP_C`.

**Key note on row-major:** Layer B applies the `(AB)ᵀ = BᵀAᵀ` operand-swap before calling the
shim.  The shim receives B before A, and both ops set to `CUBLAS_OP_T`.  The shim does NOT
perform any additional reordering — it passes its arguments directly to cuBLAS.  This is
identical to the standard column-major idiom documented in §2.1 of `01_fortran_cuda_abi.md`.

Return value: all `rt_blas_*` functions return the `cublasStatus_t` cast to `int64_t`.
`CUBLAS_STATUS_SUCCESS = 0`; any nonzero causes Layer B to return `Result.Err(LinalgError)`.

Implement remaining level-1/2 BLAS symbols (`daxpy`, `ddot`, `dnrm2`, `dscal`, `dgemv` and
their single-precision equivalents) following the same `_64` / 32-bit conditional pattern.

**Done when:** Compiles with `nvcc -shared -Xcompiler -fPIC cublas_shim.c -lcublas`; `nm -D`
shows all `rt_blas_*` + `rt_cuda_*` symbols.

---

### T-CUDA-06: Implement cuSOLVER bindings in `cublas_shim.c`

**Estimate:** 1.5 days
**Depends on:** T-CUDA-05
**Disjoint files:** `src/runtime/scilib/cublas_shim.c` (appended section)

Add all `rt_lapack_*` symbols to `cublas_shim.c` against `cusolverDn.h`:

- `rt_lapack_handle_create` → `cusolverDnCreate(&h); return (int64_t)(uintptr_t)h`
- `rt_lapack_handle_destroy(handle)` → `cusolverDnDestroy(...)`

**Two-call workspace pattern** (bufferSize query then compute):

```c
int64_t rt_lapack_dgetrf_bufsize(int64_t handle, int64_t m, int64_t n, int64_t a_ptr, int64_t lda) {
    int Lwork = 0;
    cusolverDnDgetrf_bufferSize(h, (int)m, (int)n, A, (int)lda, &Lwork);
    return (int64_t)Lwork * sizeof(double);   // return bytes so Layer B can rt_cuda_malloc
}

int64_t rt_lapack_dgetrf(int64_t handle, int64_t m, int64_t n,
                          int64_t a_ptr, int64_t lda, int64_t ipiv_ptr) {
    // Layer B must have already allocated workspace and devInfo via rt_cuda_malloc
    // This variant uses a per-call stack approach; see workspace design note below.
    int devInfo_host = 0;
    int *devInfo; cudaMalloc(&devInfo, sizeof(int));
    cusolverDnDgetrf(h, (int)m, (int)n, A, (int)lda, Workspace, devIpiv, devInfo);
    cudaMemcpy(&devInfo_host, devInfo, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(devInfo);
    return (int64_t)devInfo_host;
}
```

**Workspace design note:** For v1 the shim allocates and frees workspace internally per call
(`cudaMalloc` + `cusolverDn*_bufferSize` query + compute + `cudaFree`).  This avoids exposing
workspace pointers in the Layer A extern signature.  This has a per-call allocation cost;
PERF-SUGAR-004 (FFI batching) covers the mitigation.  For v2 a pre-allocated workspace pool
can be introduced via `rt_lapack_workspace_preallocate(bytes: i64)`.

Implement:
- `rt_lapack_dgesv` — `cusolverDnDgetrf` + `cusolverDnDgetrs` sequence
- `rt_lapack_dgetrf` / `rt_lapack_dgetrf_bufsize`
- `rt_lapack_dgetri` — LAPACK getri via cuSolver generic (`cusolverDnXgetrf` if available,
  else manual LU inversion via getrf + getrs with identity RHS)
- `rt_lapack_dgeqrf` / `rt_lapack_dgeqrf_bufsize` — `cusolverDnDgeqrf`
- `rt_lapack_dsyevd` / `rt_lapack_dsyevd_bufsize` — `cusolverDnDsyevd`
- `rt_lapack_dgesvd` / `rt_lapack_dgesvd_bufsize` — `cusolverDnDgesvd`

Return value convention: all `rt_lapack_*` compute functions return `devInfo` as `int64_t`.
`0 = success`; `> 0 = factorization failure` (singular at pivot `devInfo`); `< 0 = argument
error`.  Layer B maps these to `LinalgError` variants.

**Done when:** Adds cleanly to `cublas_shim.c`; `nm -D` shows all `rt_lapack_*` symbols.

---

### T-CUDA-07: Implement `SIMPLE_BLAS_BACKEND` dispatch logic

**Estimate:** 0.5 day
**Depends on:** T-CUDA-02, T-CUDA-03, T-CUDA-05
**Disjoint files:** `src/runtime/scilib/backend_dispatch.c` (new file) + `scilib_shim.h`

The dispatch is a **load-time** decision, not per-call.  At `rt_blas_handle_create()` time the
selected library has already been `dlopen`'d by the Simple runtime's `spl_dlopen` mechanism.
The `SIMPLE_BLAS_BACKEND` env var controls which `.so` is loaded.  This task documents and
verifies the dispatch flow; no new dispatch code is needed inside the shims themselves.

Tasks:
1. Write `backend_dispatch.c` — a helper C program (not a shim) that validates dispatch:
   reads `SIMPLE_BLAS_BACKEND`, resolves the correct `.so` path, and calls `rt_blas_handle_create`
   via `dlopen`+`dlsym`.  Used only in manual smoke tests, not shipped in production.
2. Document in `scilib_shim.h` comments: the four dispatch states (cublas / openblas / mock /
   unset auto-detect) and the fallback chain.
3. Add a `rt_blas_backend_name() -> const char*` diagnostic symbol to all three shims:
   - `cublas_shim.c` → returns `"cublas"`
   - `openblas_shim.c` → returns `"openblas"`
   - `mock_shim.c` → returns `"mock"`
   This lets Layer B emit a one-time log line at handle-create time.

**Done when:** `SIMPLE_BLAS_BACKEND=mock` loads mock; `=openblas` loads openblas; `=cublas` loads
cublas (or fails cleanly if CUDA not available); unset auto-detects in order.

---

### T-CUDA-08: Wire `src/runtime/Cargo.toml` and `src/runtime/scilib/` into Cargo workspace

**Estimate:** 0.5 day
**Depends on:** T-CUDA-01
**Disjoint files:** `src/runtime/Cargo.toml`, `src/runtime/scilib/` build files

The existing `src/runtime/Cargo.toml` manages the runtime Rust crate.  The scilib shims are
pure C (no Rust wrapper needed for v1 — the `torch_ffi.cpp` precedent shows the runtime uses
C++ directly without a Rust crate wrapper).

Tasks:
1. Add a `build.rs` (or CMake fragment) for `src/runtime/scilib/` that:
   - Always builds `mock_shim.c` → `libspl_cublas_mock.so`
   - Builds `openblas_shim.c` → `libspl_openblas.so` when OpenBLAS is available
   - Builds `cublas_shim.c` → `libspl_cublas.so` when CUDA is available (after T-CUDA-04)
2. Set build features in `src/runtime/Cargo.toml`:
   ```toml
   [features]
   scilib_mock = []          # always on; enables mock shim build
   scilib_openblas = []      # opt-in; requires openblas pkg-config
   scilib_cuda = []          # opt-in; requires CUDA >= 11.7
   ```
3. `build/` output: `.so` files placed in `build/` alongside `build/libspl_torch.so`.
4. Add `scilib_mock` to the default features list so CI always has a working mock.

**Done when:** `cargo build -p runtime --features scilib_mock` produces
`build/libspl_cublas_mock.so`; `cargo build -p runtime --features scilib_openblas` produces
`build/libspl_openblas.so` (on a machine with OpenBLAS installed).

---

### T-CUDA-09: Configure `SIMPLE_SFFI_PATH` for test harness and set mock as default

**Estimate:** 0.5 day
**Depends on:** T-CUDA-02
**Disjoint files:** `src/app/test_runner_new/` (test harness config), test env setup

For interpreter-mode spec runs (AC-7 / OQ-D compliance):

1. `bin/simple test` must set `SIMPLE_BLAS_BACKEND=mock` when running any spec under
   `src/lib/common/linalg/` or `src/lib/nogc_sync_mut/ndarray/`.
   - Mechanism: a per-directory `.simple_test_env` file (if supported by test runner), or a
     hard-coded prefix in the test runner for `linalg/` and `ndarray/` test paths.
   - If `.simple_test_env` is not yet supported, file a feature request in
     `doc/08_tracking/feature_request/compiler_requests.md` and use the hard-coded prefix for v1.
2. `SIMPLE_SFFI_PATH` must include the `build/` directory so `libspl_cublas_mock.so` is found
   by `spl_dlopen` without a full install step.
   - Add `export SIMPLE_SFFI_PATH="${SIMPLE_SFFI_PATH}:${REPO_ROOT}/build"` to `scripts/setup.sh`
     (see T-CUDA-10).
3. Verify: run `bin/simple test src/lib/common/linalg/axpy_spec.spl` in interpreter mode — must
   not hang, must not require CUDA, must use mock symbols.

**Done when:** `bin/simple test` for linalg specs passes on a machine with no CUDA and no
OpenBLAS installed (mock-only machine).

---

### T-CUDA-10: Integrate into `scripts/setup.sh`

**Estimate:** 0.5 day
**Depends on:** T-CUDA-08, T-CUDA-09
**Disjoint files:** `scripts/setup.sh` only

Add to `scripts/setup.sh`:

1. Build the scilib mock shim unconditionally:
   ```sh
   echo "[scilib] Building mock BLAS shim..."
   gcc -shared -fPIC -O2 \
       src/runtime/scilib/mock_shim.c \
       -o build/libspl_cublas_mock.so
   ```
2. Attempt to build the OpenBLAS shim:
   ```sh
   if pkg-config --exists openblas 2>/dev/null; then
       echo "[scilib] Building OpenBLAS shim..."
       gcc -shared -fPIC -O2 \
           $(pkg-config --cflags openblas) \
           src/runtime/scilib/openblas_shim.c \
           $(pkg-config --libs openblas) \
           -o build/libspl_openblas.so
   else
       echo "[scilib] OpenBLAS not found — skipping libspl_openblas.so"
   fi
   ```
3. Attempt to build the CUDA shim (detection from T-CUDA-04):
   ```sh
   if [ -f src/runtime/scilib/cuda_version.h ]; then
       echo "[scilib] Building cuBLAS shim..."
       nvcc -shared -Xcompiler -fPIC -O2 \
           src/runtime/scilib/cublas_shim.c \
           -lcublas -lcusolver \
           -o build/libspl_cublas.so
   else
       echo "[scilib] CUDA not found — skipping libspl_cublas.so"
   fi
   ```
4. Append `build/` to `SIMPLE_SFFI_PATH` export if not already present.
5. Set `SIMPLE_BLAS_BACKEND=mock` in the local `.envrc` or equivalent if the user's env
   does not already set it (do not override an existing value).

**Done when:** `scripts/setup.sh` runs cleanly on a CPU-only machine; produces
`build/libspl_cublas_mock.so`; prints `[scilib]` status lines.

---

### T-CUDA-11: Wire scilib shim builds into `scripts/bootstrap/`

**Estimate:** 0.5 day
**Depends on:** T-CUDA-08
**Disjoint files:** `scripts/bootstrap/bootstrap-from-scratch.sh` only

After the bootstrap seed binary is compiled and deployed, the scilib shims must be built so
the self-hosted binary can run linalg specs.

Add to the post-deploy section of `scripts/bootstrap/bootstrap-from-scratch.sh`:
```sh
# Build scilib shims (mock always; openblas/cuda if available)
sh scripts/setup.sh --scilib-only
```

Add a `--scilib-only` flag to `scripts/setup.sh` that runs only the scilib build steps
(steps 1–4 of T-CUDA-10), skipping the symlink and other setup.

**Rationale:** Per `feedback_extern_bootstrap_rebuild`, after adding new `rt_*` externs a
bootstrap rebuild is required.  The scilib shims introduce `rt_blas_*` / `rt_lapack_*` / `rt_cuda_*`
externs — these are not Rust-side externs requiring a seed rebuild, but the shims must exist
in `build/` before any linalg spec can run post-bootstrap.

**Done when:** `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` followed by
`bin/simple test src/lib/common/linalg/axpy_spec.spl` succeeds on a mock-only machine.

---

### T-CUDA-12: CI matrix configuration

**Estimate:** 1 day
**Depends on:** T-CUDA-09, T-CUDA-10, T-CUDA-11
**Disjoint files:** CI configuration files only (`.github/workflows/` or equivalent)

Define three CI matrix legs for scilib:

| Leg | Machine | `SIMPLE_BLAS_BACKEND` | Shims built | Specs run |
|-----|---------|----------------------|-------------|-----------|
| `mock-only` | Any (CPU only) | `mock` | mock_shim.c only | All linalg + ndarray specs; no `#[gpu_only]` |
| `openblas-host` | Linux with `libopenblas-dev` | `openblas` | mock + openblas | All linalg + ndarray; numerics verified vs reference |
| `cuda-host` | Linux with CUDA ≥ 11.7 + GPU | `cublas` | all three | All linalg + ndarray + `#[gpu_only]` annotated specs |

For each leg:

- `mock-only`: `apt-get install gcc` only; no BLAS/CUDA packages; scripts/setup.sh builds mock.
- `openblas-host`: `apt-get install libopenblas-dev`; scripts/setup.sh detects and builds openblas
  shim; specs additionally check that `rt_blas_ddot([1,2,3], [1,2,3])` returns `14.0` (numeric
  correctness check beyond mock zeros).
- `cuda-host`: uses NVIDIA-provided Docker image or runner with CUDA toolkit 11.7+; full shim set.

Add a CI check that `nm -D build/libspl_cublas_mock.so` contains every `rt_blas_*` /
`rt_lapack_*` / `rt_cuda_*` symbol — catches any symbol added in blas/lapack task files but
forgotten in the mock.

**Done when:** CI matrix YAML is written; mock-only leg can run in the existing CI environment
without GPU or OpenBLAS.

---

### T-CUDA-13: Smoke spec — three-backend `rt_blas_dgemm` identity check

**Estimate:** 0.5 day
**Depends on:** T-CUDA-09, T-CUDA-12
**Disjoint files:** `src/lib/common/linalg/blas_backend_smoke_spec.spl` (new spec file)

Write a spec (interpreter-mode, `SIMPLE_BLAS_BACKEND=mock`) that:

1. Calls `rt_blas_handle_create` and checks return is nonzero (handle is live).
2. Calls `rt_blas_backend_name` and asserts the value matches `SIMPLE_BLAS_BACKEND`.
3. Allocates a 2×2 identity matrix via `rt_cuda_malloc` + `rt_cuda_memcpy_htod`.
4. Calls `rt_blas_dgemm` with `I @ I` (identity × identity).
5. Copies result back via `rt_cuda_memcpy_dtoh`.
6. Asserts result is all-zeros (mock returns zeros — the test checks the mock contract, not math).
7. Calls `rt_blas_handle_destroy`; asserts no crash.

This spec is the acceptance gate that the full shim call chain works end-to-end in interpreter
mode.  It uses only Layer A externs (`ffi_blas.spl`) — not the full Layer B/C linalg API — to
remain within this task file's scope.

Note: this spec deliberately asserts mock-behavior (zeros), not mathematical correctness.
Numerical correctness for openblas and cublas legs is verified in the CI matrix (T-CUDA-12).

**Done when:** `bin/simple test src/lib/common/linalg/blas_backend_smoke_spec.spl` passes with
`SIMPLE_BLAS_BACKEND=mock`; zero `skip()`; zero TODO→NOTE.

---

### T-CUDA-14: Symbol completeness verification vs blas + lapack task files

**Estimate:** 0.5 day
**Depends on:** T-CUDA-02, T-CUDA-03, T-CUDA-06, completion of `scilib_port_blas.md` and
`scilib_port_lapack.md`
**Disjoint files:** `src/runtime/scilib/verify_symbols.sh` (new script)

Write `src/runtime/scilib/verify_symbols.sh`:

```sh
#!/bin/sh
# Usage: ./verify_symbols.sh build/libspl_cublas_mock.so build/libspl_openblas.so build/libspl_cublas.so
# Checks that all three shims export the same set of rt_* symbols.
MOCK_SYMS=$(nm -D "$1" | grep ' T rt_' | awk '{print $3}' | sort)
for shim in "$2" "$3"; do
    SHIM_SYMS=$(nm -D "$shim" | grep ' T rt_' | awk '{print $3}' | sort)
    diff <(echo "$MOCK_SYMS") <(echo "$SHIM_SYMS") && echo "OK: $shim" || {
        echo "SYMBOL MISMATCH: $shim"
        exit 1
    }
done
```

Run this script:
1. At the end of `scripts/setup.sh` for all three shims (skipping any not built).
2. As a CI check in the mock-only leg — all three shims must export the same `rt_*` set.
3. Manually after any new symbol is added in `scilib_port_blas.md` or `scilib_port_lapack.md`.

Add the script to the CI mock-only leg as a required step (not advisory).

**Done when:** `verify_symbols.sh` runs cleanly on mock + openblas shims; reports diff if any
symbol is present in one but not the other.

---

## Acceptance Criteria (this task file)

- [ ] `build/libspl_cublas_mock.so` exists and exports all `rt_blas_*` / `rt_lapack_*` /
  `rt_cuda_*` symbols (T-CUDA-02)
- [ ] `build/libspl_openblas.so` builds on a machine with OpenBLAS; `nm -D` matches mock symbol
  set (T-CUDA-03, T-CUDA-14)
- [ ] `build/libspl_cublas.so` builds on a CUDA ≥ 11.7 machine; uses `_64` API (T-CUDA-05/06)
- [ ] `SIMPLE_BLAS_BACKEND=mock` is the default in `bin/simple test` for linalg/ndarray specs
  (T-CUDA-09)
- [ ] `scripts/setup.sh` builds mock unconditionally; openblas and cuda conditionally; appends
  `build/` to `SIMPLE_SFFI_PATH` (T-CUDA-10)
- [ ] `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` triggers scilib mock build (T-CUDA-11)
- [ ] CI matrix has three legs: mock-only, openblas-host, cuda-host (T-CUDA-12)
- [ ] `blas_backend_smoke_spec.spl` passes interpreter mode; zero `skip()` (T-CUDA-13)
- [ ] `verify_symbols.sh` passes as CI gate (T-CUDA-14)
- [ ] No nvfortran toolchain references anywhere in `src/runtime/scilib/` (anti-pattern 1)
- [ ] No `--mode=native` in any spec run instructions (anti-pattern 3)

---

## Risk Register

| Risk | Severity | Mitigation |
|------|----------|------------|
| **R-CUDA-1: CUDA version fragmentation** — `_64` API only in CUDA ≥ 11.7; older CI runners may have 11.0–11.6 | High | T-CUDA-04 detects version; `SIMPLE_CUDA_NO_64BIT` fallback with `i32` clamping + assertion |
| **R-CUDA-2: Mock fidelity gap** — a spec tests behavior that differs between mock (zeros) and real backend | High | Specs annotated `#[gpu_only]` when they assert numeric results; mock specs assert only shape + non-error return + mock contract values |
| **R-CUDA-3: Build system reach** — scilib build must integrate into both `setup.sh` and `bootstrap-from-scratch.sh`; breakage in either blocks all downstream specs | Medium | T-CUDA-10/11 are explicitly scoped; `--scilib-only` flag isolates the scilib build step so it cannot break unrelated bootstrap stages |
| **R-CUDA-4: Symbol set drift** — blas/lapack task files add a new symbol; one or more shims miss it | Medium | `verify_symbols.sh` (T-CUDA-14) runs as a required CI gate; any drift fails CI before any spec runs |
| **R-CUDA-5: OpenBLAS row-major vs column-major double-swap** — openblas shim accidentally applies operand swap that Layer B already applied | Low–Medium | Document clearly in `openblas_shim.c` header comment; CI openblas-host leg verifies `I @ I = I` numerically |
| **R-CUDA-6: cuSOLVER workspace per-call malloc cost** — each `rt_lapack_dgetrf` call allocates and frees a CUDA workspace | Low | Acceptable for v1; PERF-SUGAR-004 tracks batching mitigation; internal workspace is freed before function returns |
