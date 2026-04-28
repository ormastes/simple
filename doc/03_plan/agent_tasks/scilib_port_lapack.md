# Agent Task File: scilib_port_lapack

**Area:** `std.linalg` — LAPACK-level bindings  
**Phase:** 4-spec + 5-implement (parallel with `scilib_port_blas.md`)  
**Owner:** scilib-lapack agent  
**Date:** 2026-04-27  
**Status:** ready (gated on T-PERFSUGAR-01 and T-NDARRAY complete)

---

## Scope

LAPACK Layer A/B/C for: `gesv`, `getrf`, `geqrf`, `syevd`, `gesvd`, `getri`, `inv`, `solve`.  
Typed wrappers: `Pivot`, `Workspace<T>`, `LapackInfo`, `LinalgError`.  
Workspace query-then-compute lifecycle.  
Backend dispatch: cuSOLVER (CUDA) → LAPACKE (host) → mock (interp).  
Row-major external contract via operand-swap (OQ-C).  
Interp-mode AC-7 compliance via mock backend (OQ-D).

**Out of scope (disjoint from siblings):**
- `libspl_cublas.so` / `libspl_lapack.so` shim crate build system → `scilib_port_cuda_fortran.md`
- BLAS externs (`rt_blas_dgemm`, etc.) → `scilib_port_blas.md`
- `BlasHandle` singleton lifecycle → `scilib_port_blas.md`
- `NDArray<T>`, `Matrix<T>`, `Vector<T>`, `Shape`, `Index`, `Float64` definitions → `scilib_port_ndarray.md`
- `math{}` `App("inv"|"solve")` arms → `scilib_port_math_block.md`
- `DataFrame`, `Series`, `std.df` → `scilib_port_df.md`
- `--mode=native` is NEVER an option for spec acceleration (AC-7 / feedback_compile_mode_false_greens)
- nvfortran direct binding (rejected at D-1)

---

## Hard Gates (must be resolved before any impl task begins)

| Gate | Source | Required status |
|------|--------|----------------|
| PERF-SUGAR-001 (`rt_f64_array_alloc`) | T-PERFSUGAR-01 | `fixed` + bootstrap rebuild |
| `NDArray<T>`, `Matrix<T>`, `Vector<T>`, `Index`, `Shape` | T-NDARRAY-01 through T-NDARRAY-05 | `done` |
| `rt_blas_handle_create` / `BlasHandle` singleton | T-BLAS-01 | `done` (shared handle used for cuSOLVER init) |
| Row-major ↔ column-major operand-swap helper | T-BLAS-03 | `done` (reused here for LAPACK driver wrappers) |

---

## Cross-Area Dependency Map

| This task depends on | Provides to |
|----------------------|-------------|
| T-PERFSUGAR-01 | T-LAPACK-01 (Workspace typed buffer) |
| T-NDARRAY-01..05 | T-LAPACK-02..08 (all wrappers consume NDArray types) |
| T-BLAS-01 (handle) | T-LAPACK-04 (cuSOLVER handle wraps BlasHandle context) |
| T-BLAS-03 (op-swap) | T-LAPACK-06..08 (LAPACK drivers need row↔col conversion at call site) |
| T-CUDA-NN (shim crate) | T-LAPACK-09 (real backend integration, not needed for mock specs) |
| T-LAPACK-01..10 | T-MATHBLOCK-NN (`App("inv"|"solve")` eval arms) |
| T-LAPACK-01..10 | T-ML-NN (`LinearRegression.fit` uses `linalg.solve`; `Ridge` uses `linalg.gesv`) |

---

## Dependency Graph (topo order)

```
[GATE] T-PERFSUGAR-01, T-NDARRAY done, T-BLAS-01/03 done
  │
  ├─ T-LAPACK-01  (LinalgError + LapackInfo typed wrappers)
  ├─ T-LAPACK-02  (Pivot typed wrapper — hides 1-based Fortran indexing + device/host)
  ├─ T-LAPACK-03  (Workspace<T> typed wrapper — bufferSize query lifecycle)
  │
  ├─ T-LAPACK-04  (cuSOLVER handle init + Layer A extern decls: bufferSize + compute pairs)
  │
  ├─ T-LAPACK-05  (mock shim symbols — required before any spec is written)
  │
  ├─[parallel, after 04+05]
  │   ├─ T-LAPACK-06  (getrf Layer B — LU factorization; uses Pivot + Workspace)
  │   ├─ T-LAPACK-07  (gesv Layer B — linear solve; wraps getrf + getrs; hides Pivot)
  │   ├─ T-LAPACK-08  (getri Layer B — matrix inverse from LU; used by inv)
  │   ├─ T-LAPACK-09  (geqrf Layer B — QR; tau vector, row-major contract)
  │   ├─ T-LAPACK-10  (syevd Layer B — symmetric eigenvalue; jobz dispatch)
  │   └─ T-LAPACK-11  (gesvd Layer B — SVD; jobu/jobvt dispatch; U, s, Vt outputs)
  │
  ├─[after 07+08] T-LAPACK-12  (Layer C: gesv, getrf, inv, solve — public API; no primitives)
  ├─[after 09]    T-LAPACK-13  (Layer C: geqrf, qr public wrapper)
  ├─[after 10+11] T-LAPACK-14  (Layer C: syevd, gesvd — public API)
  │
  ├─[after 12+13+14] T-LAPACK-15  (specs: gesv + solve interpreter-mode under mock backend)
  ├─[after 12+13+14] T-LAPACK-16  (specs: getrf + inv interpreter-mode)
  ├─[after 12+13+14] T-LAPACK-17  (specs: geqrf/syevd/gesvd interpreter-mode; mock invariant checks)
  │
  ├─[after 15..17 green] T-LAPACK-18  (LAPACKE host backend integration — openblas shim symbols)
  └─[after 18] T-LAPACK-19  (cuSOLVER backend integration — real GPU path, #[gpu_only] specs)
```

---

## Task List

---

### T-LAPACK-01 — Define `LinalgError` enum and `LapackInfo` typed decoder

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/types.spl`  
**Deps:** T-NDARRAY-01 (`Index` wrapper available)

Define `LinalgError` and `LapackInfo` as typed enums. No `i64` INFO integer ever reaches Layer C.

```
enum LinalgError:
    Singular(row: Index)             # INFO > 0: U[INFO,INFO] is zero
    BadArgument(arg: Index)          # INFO < 0: illegal argument position
    NotConverged(iterations: Index)  # syevd/gesvd: eigenvalue/SVD iteration failed
    DimensionMismatch(a: Shape, b: Shape)
    UnsupportedDType(d: DType)
    WorkspaceError                   # bufferSize returned negative or zero

struct LapackInfo:
    _raw: i64   # internal only
```

`LapackInfo.decode() -> Result<Unit, LinalgError>` maps `raw == 0` to `Ok`, `raw > 0` to `Singular(Index(_raw))`, `raw < 0` to `BadArgument(Index(-_raw))`.

AC: `LinalgError` has no `i64`/primitive fields in any public variant. `LapackInfo` is not exported from `mod.spl` (internal Layer B only).

---

### T-LAPACK-02 — Define `Pivot` typed wrapper (hides 1-based indexing + device/host residency)

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/types.spl`  
**Deps:** T-LAPACK-01, T-NDARRAY-01 (`Index`, `Device`)

`Pivot` wraps the IPIV permutation array returned by `getrf`/`gesv`. Fortran/cuSOLVER use 1-based indices; LAPACKE uses the same 1-based convention. The wrapper must:
- Store raw pivot data internally as `_data: [i64]` (private)
- Track `_device: Device` (host or CUDA — cuSOLVER devIpiv stays on device until explicitly transferred)
- Expose `fn at(i: Index) -> Index` returning **0-based** `Index` (subtract 1 internally)
- Expose `fn len() -> Index`
- Never expose `_data` directly

```
struct Pivot:
    _data:   [i64]    # internal; 1-based from Fortran/cuSOLVER
    _device: Device   # CPU or CUDA(n)

fn Pivot.at(i: Index) -> Index   # 0-based
fn Pivot.len() -> Index
```

AC: No `[i64]`, `[i32]`, or raw integer arrays appear in any Layer C signature. `Pivot._device` is CPU for LAPACKE path; CUDA for cuSOLVER path. Host-to-device copy happens in Layer B before `getrs` call.

---

### T-LAPACK-03 — Define `Workspace<T>` typed wrapper (bufferSize query lifecycle)

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/types.spl`  
**Deps:** T-PERFSUGAR-01 (typed buffer ctor), T-NDARRAY-01 (`Index`, `Device`)

cuSOLVER requires an explicit two-call pattern: first query the required workspace size (`*_bufferSize`), then allocate and pass the buffer to the compute call. LAPACKE auto-allocates internally (pass `lwork = -1` to query or use `LAPACK_WORK_MEMORY_ERROR`). `Workspace<T>` unifies both:

```
struct Workspace<T>:
    _buf:    [T]      # internal backing buffer; typed, not raw bytes
    _lwork:  Index    # actual allocated length
    _device: Device   # CPU or CUDA (cuSOLVER workspace is device-resident)
```

`Workspace.alloc(lwork: Index, device: Device) -> Workspace<Float64>` uses `rt_f64_array_alloc` (PERF-SUGAR-001) for CPU; `rt_cuda_malloc` for CUDA.  
`Workspace.ptr() -> i64` returns the buffer pointer for Layer A extern calls (internal use only).  
`Workspace<T>` is never exported from `mod.spl`.

AC: Layer C functions have no `lwork` parameter. Workspace is allocated in Layer B after the bufferSize query, passed to compute call, then dropped. No raw `i64` buffer size reaches the caller.

---

### T-LAPACK-04 — Layer A: cuSOLVER handle init + all `rt_lapack_*` extern decls

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/ffi_lapack.spl`  
**Deps:** T-BLAS-01 (BlasHandle structure reference), T-LAPACK-01..03

Declare all Layer A `extern fn` bindings. Each LAPACK kernel has two externs: a `_buffersize` query and a compute call.  All pointer arguments are `i64` (opaque pointer-as-integer). All dimension arguments are `i64` (64-bit, matching cuSOLVER `_64` API where available).

```
# Handle
extern fn rt_lapack_handle_create() -> i64
extern fn rt_lapack_handle_destroy(handle: i64) -> i64

# LU factorization (getrf)
extern fn rt_lapack_dgetrf_buffersize(handle: i64, m: i64, n: i64, a_ptr: i64, lda: i64) -> i64
extern fn rt_lapack_dgetrf(handle: i64, m: i64, n: i64, a_ptr: i64, lda: i64,
                            work_ptr: i64, lwork: i64, ipiv_ptr: i64, info_ptr: i64) -> i64

# Triangular solve (getrs — internal, used by gesv and inv)
extern fn rt_lapack_dgetrs(handle: i64, trans: i64, n: i64, nrhs: i64,
                            a_ptr: i64, lda: i64, ipiv_ptr: i64,
                            b_ptr: i64, ldb: i64, info_ptr: i64) -> i64

# Linear solve combining getrf+getrs (gesv)
extern fn rt_lapack_dgesv_buffersize(handle: i64, n: i64, nrhs: i64,
                                     a_ptr: i64, lda: i64, b_ptr: i64, ldb: i64) -> i64
extern fn rt_lapack_dgesv(handle: i64, n: i64, nrhs: i64,
                           a_ptr: i64, lda: i64, ipiv_ptr: i64,
                           b_ptr: i64, ldb: i64, work_ptr: i64, lwork: i64, info_ptr: i64) -> i64

# Matrix inverse from LU (getri)
extern fn rt_lapack_dgetri_buffersize(handle: i64, n: i64, a_ptr: i64, lda: i64) -> i64
extern fn rt_lapack_dgetri(handle: i64, n: i64, a_ptr: i64, lda: i64,
                            ipiv_ptr: i64, work_ptr: i64, lwork: i64, info_ptr: i64) -> i64

# QR factorization (geqrf)
extern fn rt_lapack_dgeqrf_buffersize(handle: i64, m: i64, n: i64, a_ptr: i64, lda: i64) -> i64
extern fn rt_lapack_dgeqrf(handle: i64, m: i64, n: i64, a_ptr: i64, lda: i64,
                            tau_ptr: i64, work_ptr: i64, lwork: i64, info_ptr: i64) -> i64

# Orgqr: form Q from geqrf output (needed for full QR decomposition)
extern fn rt_lapack_dorgqr_buffersize(handle: i64, m: i64, n: i64, k: i64,
                                      a_ptr: i64, lda: i64, tau_ptr: i64) -> i64
extern fn rt_lapack_dorgqr(handle: i64, m: i64, n: i64, k: i64, a_ptr: i64, lda: i64,
                            tau_ptr: i64, work_ptr: i64, lwork: i64, info_ptr: i64) -> i64

# Symmetric eigenvalue decomposition (syevd)
# jobz: 0=eigenvalues only, 1=eigenvalues+eigenvectors
# uplo: 0=upper, 1=lower
extern fn rt_lapack_dsyevd_buffersize(handle: i64, jobz: i64, uplo: i64,
                                      n: i64, a_ptr: i64, lda: i64) -> i64
extern fn rt_lapack_dsyevd(handle: i64, jobz: i64, uplo: i64, n: i64,
                            a_ptr: i64, lda: i64, w_ptr: i64,
                            work_ptr: i64, lwork: i64, info_ptr: i64) -> i64

# Singular value decomposition (gesvd)
# jobu/jobvt: 0=none, 1=all, 2=min(m,n) columns/rows (S mode)
extern fn rt_lapack_dgesvd_buffersize(handle: i64, jobu: i64, jobvt: i64,
                                      m: i64, n: i64, a_ptr: i64, lda: i64) -> i64
extern fn rt_lapack_dgesvd(handle: i64, jobu: i64, jobvt: i64, m: i64, n: i64,
                            a_ptr: i64, lda: i64, s_ptr: i64,
                            u_ptr: i64, ldu: i64, vt_ptr: i64, ldvt: i64,
                            work_ptr: i64, lwork: i64, info_ptr: i64) -> i64
```

AC: No `extern fn` has non-primitive parameter or return types. Each LAPACK kernel that needs a workspace has both `_buffersize` and compute variants. `trans`, `jobz`, `jobu`, `jobvt`, `uplo` are encoded as `i64` constants (Layer B defines the mapping enums).

---

### T-LAPACK-05 — Mock shim: deterministic stub symbols for interp-mode specs

**Effort:** ≤ 1 day  
**Files:** `src/runtime/scilib/mock_shim.c` (extend existing; coordinate with T-BLAS agent to avoid double-write of shared file)  
**Deps:** T-LAPACK-04 (symbol list)  
**Note:** Coordinate with `scilib_port_blas.md` agent — the mock shim is a shared C file. LAPACK agent appends `rt_lapack_*` symbols; BLAS agent appends `rt_blas_*` symbols. Assign disjoint symbol blocks; no parallel edits to the same file.

Mock behavior per kernel:

| Symbol | Mock return |
|--------|------------|
| `rt_lapack_handle_create` | `1` (non-null sentinel) |
| `rt_lapack_dgetrf_buffersize` | `n * n` (safe overestimate) |
| `rt_lapack_dgetrf` | fills `ipiv` with identity permutation (1-based: 1,2,3…n); `info = 0` |
| `rt_lapack_dgetrs` | copies `b` to output unchanged (identity op); `info = 0` |
| `rt_lapack_dgesv_buffersize` | `n * nrhs` |
| `rt_lapack_dgesv` | copies `b` to output; `info = 0` |
| `rt_lapack_dgetri_buffersize` | `n * n` |
| `rt_lapack_dgetri` | writes identity matrix into `a`; `info = 0` |
| `rt_lapack_dgeqrf_buffersize` | `m * n` |
| `rt_lapack_dgeqrf` | writes zeros to `tau`; `a` unchanged; `info = 0` |
| `rt_lapack_dorgqr_buffersize` | `m * n` |
| `rt_lapack_dorgqr` | writes identity into `a`; `info = 0` |
| `rt_lapack_dsyevd_buffersize` | `n * n + n` |
| `rt_lapack_dsyevd` | writes zeros to `w`; writes identity into `a`; `info = 0` |
| `rt_lapack_dgesvd_buffersize` | `5 * (m + n)` |
| `rt_lapack_dgesvd` | `s` = ones; `U` = identity (m×m); `Vt` = identity (n×n); `info = 0` |

**Risk flag (mock invariant quality):** syevd and gesvd mock outputs must satisfy structural invariants so spec assertions are non-vacuous. Specifically: `s` must be non-negative (uses ones, satisfying `s[i] >= 0`); `U` and `Vt` must be orthogonal (identity satisfies `UUᵀ = I`, `VᵀV = I`). Spec assertions must check these invariants, not just that the call returned `Ok`. If mock is too lenient, the real backend can silently produce wrong results while passing all specs.

AC: All `rt_lapack_*` symbols present in mock shim. `SIMPLE_BLAS_BACKEND=mock` causes all specs to pass without a GPU. Mock returns are deterministic (no random values). Identity-based mock strategy documented in a comment block in `mock_shim.c`.

---

### T-LAPACK-06 — Layer B: `getrf` wrapper (LU factorization)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-02 (Pivot), T-LAPACK-03 (Workspace), T-LAPACK-04 (externs), T-LAPACK-05 (mock)

Layer B internal function (not exported at Layer C):

```
fn _lapack_getrf(handle: i64, a: Matrix<Float64>) -> Result<(Matrix<Float64>, Pivot), LinalgError>
```

Steps:
1. Assert `a` is row-major contiguous. If not, call `.contiguous()` to copy.
2. Apply OQ-C column-major conversion: transpose `a` in-place (or use `(AB)ᵀ = BᵀAᵀ` idiom — for a single matrix, pass transposed dimensions so LAPACK sees a column-major view of the row-major buffer without copying).
3. Query workspace: call `rt_lapack_dgetrf_buffersize`; decode returned `i64` into `Workspace<Float64>` via T-LAPACK-03.
4. Allocate `ipiv` buffer (`[i64]` of length `min(m,n)`, internal).
5. Call `rt_lapack_dgetrf`.
6. Decode `info` via `LapackInfo.decode() -> Result<Unit, LinalgError>`.
7. Wrap `ipiv` in `Pivot` (device = CPU for LAPACKE path; CUDA for cuSOLVER path; carry from handle context).
8. Return `(LU_matrix_as_Matrix<Float64>, Pivot)`.

AC: `Pivot._data` is 1-based raw from the extern; `Pivot.at()` corrects to 0-based. No `i64` from `ipiv` buffer reaches Layer C. Workspace dropped after call. Row-major externally; column-major at extern boundary.

---

### T-LAPACK-07 — Layer B: `gesv` wrapper (linear solve AX=B, hides Pivot)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-06 (getrf internally reusable), T-LAPACK-04 (rt_lapack_dgesv)

Layer B internal function:

```
fn _lapack_gesv(handle: i64, a: Matrix<Float64>, b: Matrix<Float64>)
    -> Result<Matrix<Float64>, LinalgError>
```

Two implementation paths:
- **cuSOLVER path:** call `rt_lapack_dgesv_buffersize` then `rt_lapack_dgesv` directly (one-call solve; LAPACK internally does LU).
- **LAPACKE path:** call `_lapack_getrf` (to get LU + Pivot), then `rt_lapack_dgetrs` with the Pivot buffer. This reuses T-LAPACK-06.

Path selection governed by handle context (`_device == CUDA` → cuSOLVER; else LAPACKE).

Dimension checks (Layer B only — never leave to the extern):
- `a` must be square (`m == n`).
- `b.rows == a.rows`.
- Emit `LinalgError.DimensionMismatch` immediately if not satisfied.

OQ-C operand-swap: for LAPACKE path, `a` is passed column-major (transpose without copy as in T-LAPACK-06); `b` is also column-major (nrhs columns become rows in Fortran view). Layer B handles this swap; Layer C passes row-major inputs and receives row-major output.

AC: `Pivot` never returned to caller. `lwork` never visible at Layer C. Dimension errors raised before any FFI call. Row-major in, row-major out at Layer C boundary.

---

### T-LAPACK-08 — Layer B: `getri` wrapper (matrix inverse from LU)

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-06 (getrf to get LU + Pivot before calling getri)

Layer B internal function:

```
fn _lapack_getri(handle: i64, a: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>
```

Steps:
1. Call `_lapack_getrf(handle, a)` → `(LU, pivot)`.
2. Query getri workspace: `rt_lapack_dgetri_buffersize`.
3. Allocate `Workspace<Float64>`.
4. Extract `pivot._data` (internal `[i64]`) for the extern call (1-based, as Fortran expects).
5. Call `rt_lapack_dgetri` with `LU` buffer, `pivot._data` pointer, workspace.
6. Decode info → `LinalgError`.
7. Return result as `Matrix<Float64>`.

Note: `inv` (Layer C) calls this. The architecture §5 table specifies `inv = dgetrf + dgetri`.

AC: `Pivot._data` accessed only inside this Layer B function. No pivot indexing leaks to Layer C. Workspace dropped. Square-matrix check before getrf call.

---

### T-LAPACK-09 — Layer B: `geqrf` wrapper (QR factorization)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-04 (geqrf + orgqr externs), T-LAPACK-03 (Workspace)

Layer B internal function:

```
fn _lapack_geqrf(handle: i64, a: Matrix<Float64>)
    -> Result<(Matrix<Float64>, Vector<Float64>), LinalgError>
```

Steps:
1. OQ-C column-major conversion (same pattern as getrf).
2. Query `rt_lapack_dgeqrf_buffersize` → allocate `Workspace<Float64>`.
3. Allocate tau buffer: `[f64]` of length `min(m,n)` (internal).
4. Call `rt_lapack_dgeqrf`. Decode info.
5. Wrap tau as `Vector<Float64>` (Layer B wraps `f64` elements with `Float64`).
6. Return `(compact_QR_matrix, tau_vector)`.

Note: To form explicit Q from the compact representation, `_lapack_orgqr` is a separate internal function that calls `rt_lapack_dorgqr`. Layer C `geqrf` returns the compact form; a separate `qr_explicit` Layer C function (if needed) calls orgqr additionally.

AC: tau buffer is `Vector<Float64>` at Layer C (no raw `[f64]`). Workspace dropped. Column-major handled in Layer B only.

---

### T-LAPACK-10 — Layer B: `syevd` wrapper (symmetric eigenvalue decomposition)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-04 (syevd externs), T-LAPACK-03 (Workspace)

Layer B internal function:

```
fn _lapack_syevd(handle: i64, a: Matrix<Float64>, compute_vecs: Bool)
    -> Result<(Vector<Float64>, Matrix<Float64>), LinalgError>
```

`compute_vecs = True` → `jobz = 1` (CUSOLVER_EIG_MODE_VECTOR); `False` → `jobz = 0`.

Steps:
1. Assert `a` is square. Column-major conversion (OQ-C).
2. Query `rt_lapack_dsyevd_buffersize(handle, jobz, uplo=0, n, a_ptr, lda)` → workspace size.
3. Allocate `Workspace<Float64>`.
4. Allocate eigenvalue buffer `w: [f64]` (internal, length `n`).
5. Call `rt_lapack_dsyevd`. Decode info — `NotConverged` if `info > 0`.
6. Wrap `w` as `Vector<Float64>` (elementwise `Float64` wrapping, using `rt_f64_array_alloc` + loop).
7. Return `(eigenvalues, eigenvectors_or_empty_matrix)`.

**Risk flag (workspace jobz interaction):** bufferSize depends on `jobz`. `jobz=0` (values only) requests a smaller workspace than `jobz=1` (vectors). Wrong jobz at bufferSize step causes SIGSEGV or incorrect `lwork`. Always call bufferSize with the same `jobz` value as the compute call.

AC: `LinalgError.NotConverged` raised when info > 0 (convergence failure). `uplo` defaults to upper triangular (0) and is not exposed at Layer C. `jobz` mapped from `compute_vecs: Bool`, not exposed as `i64`.

---

### T-LAPACK-11 — Layer B: `gesvd` wrapper (SVD)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/lapack.spl`  
**Deps:** T-LAPACK-04 (gesvd externs), T-LAPACK-03 (Workspace)

Layer B internal function:

```
fn _lapack_gesvd(handle: i64, a: Matrix<Float64>)
    -> Result<(Matrix<Float64>, Vector<Float64>, Matrix<Float64>), LinalgError>
```

Returns `(U, s, Vt)` where `U` is `m×m`, `s` is `min(m,n)`, `Vt` is `n×n`.

Steps:
1. OQ-C column-major conversion.
2. `jobu = 1` (all columns of U), `jobvt = 1` (all rows of Vt).
3. Query `rt_lapack_dgesvd_buffersize` → workspace.
4. Allocate `s: [f64]` length `min(m,n)` (internal), U and Vt output buffers.
5. Call `rt_lapack_dgesvd`. Decode info — `NotConverged` if `info > 0`.
6. Wrap `s` as `Vector<Float64>`, U and Vt as `Matrix<Float64>`.
7. Return `(U, s, Vt)`.

**Risk flag (workspace jobz interaction):** bufferSize for gesvd depends on `jobu`/`jobvt`. If the mock shim hard-codes a buffer size that is too small for the real backend's jobu=1/jobvt=1 call, the real backend will SIGSEGV. Mock must return a size that satisfies the compute call's actual requirement — use `5 * (m + n)` as a safe overestimate (as listed in T-LAPACK-05).

AC: Singular values in `s` are non-negative (LAPACK guarantees). If spec asserts `s[0] >= Float64(0.0)`, this is testable even with mock. `NotConverged` on non-convergence. No raw singular-value `f64` at Layer C.

---

### T-LAPACK-12 — Layer C: public API for `gesv`, `getrf`, `inv`, `solve`

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/mod.spl`  
**Deps:** T-LAPACK-07 (gesv Layer B), T-LAPACK-08 (getri Layer B), T-LAPACK-06 (getrf Layer B)

Public Layer C functions (no primitives anywhere):

```
# Solve AX = B; A is n×n, B is n×nrhs; returns X of same shape as B
fn gesv(a: Matrix<Float64>, b: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>

# LU factorization; returns (LU, Pivot) for use with explicit getrs if needed
fn getrf(a: Matrix<Float64>) -> Result<(Matrix<Float64>, Pivot), LinalgError>

# Matrix inverse; internally uses getrf + getri
fn inv(a: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>

# Solve Ax = b for vector b (convenience alias over gesv with nrhs=1)
fn solve(a: Matrix<Float64>, b: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>
```

`solve` promotes `b: Vector<Float64>` to `Matrix<Float64>` (n×1), calls `_lapack_gesv`, demotes result back to `Vector<Float64>`.

`Pivot` is exported from `mod.spl` (it appears in `getrf` return type). `LapackInfo` and `Workspace<T>` are NOT exported.

AC: All four functions are primitive-free. `LinalgError` is the only error type. `Pivot` in `getrf` return is fully typed. `solve` is a true alias — shares Layer B impl with `gesv`, no code duplication.

---

### T-LAPACK-13 — Layer C: public API for `geqrf`

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/mod.spl`  
**Deps:** T-LAPACK-09 (geqrf Layer B)

```
# QR factorization; returns (compact_QR, tau)
fn geqrf(a: Matrix<Float64>) -> Result<(Matrix<Float64>, Vector<Float64>), LinalgError>
```

`tau` is the Householder reflector coefficient vector (length `min(m,n)`), typed as `Vector<Float64>`. Layer C does not expose `orgqr` directly in v1; explicit Q formation is left to a separate `qr_explicit` helper if needed by T-ML-NN.

AC: No `lwork`, no `i64` tau buffer. `tau` is `Vector<Float64>`.

---

### T-LAPACK-14 — Layer C: public API for `syevd` and `gesvd`

**Effort:** ≤ 1 day  
**Files:** `src/lib/common/linalg/mod.spl`  
**Deps:** T-LAPACK-10 (syevd Layer B), T-LAPACK-11 (gesvd Layer B)

```
# Symmetric eigenvalue decomposition; returns (eigenvalues, eigenvectors)
fn syevd(a: Matrix<Float64>) -> Result<(Vector<Float64>, Matrix<Float64>), LinalgError>

# SVD; returns (U, singular_values, Vt)
fn gesvd(a: Matrix<Float64>) -> Result<(Matrix<Float64>, Vector<Float64>, Matrix<Float64>), LinalgError>
```

`syevd` always computes eigenvectors (`jobz=1`). A future `syevd_values_only` Layer C variant (not in v1) would pass `jobz=0` for performance.

AC: Both functions primitive-free. `LinalgError.NotConverged` is the only failure mode beyond `Singular`/`DimensionMismatch`.

---

### T-LAPACK-15 — Specs: `gesv` and `solve` (interpreter mode, mock backend)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/gesv_spec.spl`, `src/lib/common/linalg/solve_spec.spl`  
**Deps:** T-LAPACK-12 (Layer C available), T-LAPACK-05 (mock green)  
**Test mode:** `bin/simple test` (interpreter mode); `SIMPLE_BLAS_BACKEND=mock`

Spec cases for `gesv`:
- 2×2 identity system: `gesv(I₂, B)` → `X == B` (mock identity result).
- Dimension mismatch: non-square A → `Err(DimensionMismatch)` without calling any extern.
- Shape mismatch: `A.rows != B.rows` → `Err(DimensionMismatch)`.
- Mock singular: inject mock `info = 1` → `Err(Singular(Index(1)))`.

Spec cases for `solve`:
- `solve(I₂, v)` → `x == v` (identity solve).
- `solve(A, v)` with wrong dimensions → `Err(DimensionMismatch)`.

All assertions use typed wrappers: `Float64(0.0)` not `0.0`; `Index(1)` not `1`. No `skip()`. No `--mode=native`.

AC: All spec cases pass under `bin/simple test` with `SIMPLE_BLAS_BACKEND=mock`. No `skip()`. No primitive literals in any `it` block assertion. Mock singular injection verified.

---

### T-LAPACK-16 — Specs: `getrf` and `inv` (interpreter mode, mock backend)

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/getrf_spec.spl`, `src/lib/common/linalg/inv_spec.spl`  
**Deps:** T-LAPACK-12 (Layer C), T-LAPACK-05 (mock)

Spec cases for `getrf`:
- 3×3 matrix: `getrf(A)` returns `Ok((LU, pivot))`. Assert `pivot.len() == Index(3)`. Assert `pivot.at(Index(0)) >= Index(0)` (0-based check).
- Non-square: not an error (getrf accepts m×n); check `pivot.len() == Index(min(m,n))`.
- Mock singular (`info=1`): `Err(Singular(Index(1)))`.

Spec cases for `inv`:
- `inv(I₃)` → identity (mock returns identity; assert `result == identity_matrix`).
- Non-square `inv`: `Err(DimensionMismatch)` before any extern call.
- Mock singular: `Err(Singular(...))`.

AC: `Pivot.at()` returns `Index` not `i64`. `inv` dim-check fires without FFI call. Zero `skip()`.

---

### T-LAPACK-17 — Specs: `geqrf`, `syevd`, `gesvd` with mock invariant assertions

**Effort:** ≤ 2 days  
**Files:** `src/lib/common/linalg/geqrf_spec.spl`, `src/lib/common/linalg/syevd_spec.spl`, `src/lib/common/linalg/gesvd_spec.spl`  
**Deps:** T-LAPACK-13, T-LAPACK-14 (Layer C), T-LAPACK-05 (mock)

**geqrf specs:**
- `geqrf(A)` → `Ok((QR, tau))`. Assert `tau.len() == Index(min(m,n))`.
- Mock returns zero tau and unchanged A; verify result shape correct.

**syevd specs (mock invariant check):**
- `syevd(I₂)` → `Ok((vals, vecs))`. Assert `vals.len() == Index(2)`. Assert `vecs.shape() == Shape(2,2)`.
- Assert each singular value `vals[i] >= Float64(0.0)` — this is checked even in mock (mock returns zeros for w, which satisfies `>= 0`).
- **Not-converged path:** inject mock `info=1` → `Err(NotConverged(Index(1)))`.

**gesvd specs (mock invariant check):**
- `gesvd(A_2x3)` → `Ok((U, s, Vt))`. Assert shapes: `U` is `2×2`, `s.len() == Index(2)`, `Vt` is `3×3`.
- Assert `s[0] >= Float64(0.0)` and `s[1] >= Float64(0.0)`.
- U orthogonality check (mock returns identity): assert `U.shape() == Shape(2,2)`.
- Not-converged path: `Err(NotConverged(...))`.

AC: All assertions non-vacuous (they would fail if mock returned wrong shapes). Zero `skip()`. `NotConverged` path tested for both syevd and gesvd. `Float64`/`Index`/`Shape` wrappers throughout.

---

### T-LAPACK-18 — LAPACKE host backend integration (openblas shim symbols)

**Effort:** ≤ 2 days  
**Files:** `src/runtime/scilib/openblas_shim.c` (coordinate with T-CUDA agent — T-CUDA-NN builds this file)  
**Deps:** T-LAPACK-04 (symbol names), T-CUDA-NN (shim crate build; LAPACK agent adds LAPACKE symbol implementations)  
**Note:** This task begins only after mock-backend specs (T-LAPACK-15..17) are all green. It adds LAPACKE implementations behind the same `rt_lapack_*` symbol set.

`libspl_openblas.so` exposes same `rt_lapack_*` symbols as the mock shim, but calls `LAPACKE_dgesv`, `LAPACKE_dgetrf`, `LAPACKE_dgetri`, `LAPACKE_dgeqrf`, `LAPACKE_dsyevd`, `LAPACKE_dgesvd` (from `lapacke.h` / OpenBLAS).

LAPACKE auto-allocates workspace (pass `lwork = LAPACK_WORK_MEMORY_ERROR` query convention). The `rt_lapack_*_buffersize` stubs in the LAPACKE shim return `0` (LAPACKE manages internally); the compute `rt_lapack_*` functions pass `work_ptr = NULL, lwork = -1` to LAPACKE.

Column-major convention: LAPACKE accepts `LAPACK_ROW_MAJOR` or `LAPACK_COL_MAJOR` flag. Pass `LAPACK_ROW_MAJOR` so the openblas shim receives row-major buffers directly (no operand swap needed in Layer B for LAPACKE path — only for cuSOLVER). Layer B must distinguish path via handle type.

Pivot convention: LAPACKE returns 1-based `lapack_int` IPIV; shim copies to `int64_t` array passed in. Same 1-based convention as cuSOLVER; `Pivot` wrapping in Layer B is path-agnostic.

AC: `SIMPLE_BLAS_BACKEND=openblas` runs all v1 spec cases (identity systems, pivot check) with real LAPACKE. CI gate: this target runs on CPU-only CI with OpenBLAS installed.

---

### T-LAPACK-19 — cuSOLVER backend integration (real GPU path, #[gpu_only] specs)

**Effort:** ≤ 2 days  
**Files:** `src/runtime/scilib/cublas_shim.c` (coordinate with T-CUDA-NN), `src/lib/common/linalg/gesv_gpu_spec.spl`  
**Deps:** T-LAPACK-18 (openblas path green first), T-CUDA-NN (cuSOLVER shim crate)

Add cuSOLVER implementations for `rt_lapack_dgesv`, `rt_lapack_dgetrf`, `rt_lapack_dgetri`, `rt_lapack_dgeqrf`, `rt_lapack_dsyevd`, `rt_lapack_dgesvd` inside `libspl_cublas.so`.

cuSOLVER pattern for each kernel:
1. `cusolverDnDgetrf_bufferSize` (device workspace query).
2. `cudaMalloc` for workspace and devIpiv (device-resident).
3. `cusolverDnDgetrf` (compute on device).
4. `cudaMemcpy` to copy devIpiv to host if Layer B needs it for `getrs`.
5. Check `devInfo` via `cudaMemcpy` to host.

`#[gpu_only]` spec (separate file; excluded from `bin/simple test`; runs in CI GPU stage):
- `gesv` with real 3×3 system and known exact solution. Verify `X` matches known solution to `Float64` tolerance.
- `gesvd` of a known matrix with precomputed singular values.

AC: `SIMPLE_BLAS_BACKEND=cublas` passes GPU specs. `bin/simple test` never runs these specs (they are annotated `#[gpu_only]` and excluded by the test runner). No perf regression in mock path from adding the cuSOLVER path.

---

## Acceptance Criteria Summary (v1 gate)

- [ ] All `rt_lapack_*` externs declared in `ffi_lapack.spl` (Layer A); no primitive-typed params at Layer B/C boundary
- [ ] `LinalgError`, `LapackInfo`, `Pivot`, `Workspace<T>` defined; `LapackInfo` and `Workspace<T>` not exported from `mod.spl`
- [ ] `Pivot.at()` returns 0-based `Index`; `Pivot._data` (1-based raw) never exposed
- [ ] `Workspace<T>` allocated after bufferSize query; dropped after compute call; never visible at Layer C
- [ ] Seven Layer C functions (`gesv`, `getrf`, `geqrf`, `syevd`, `gesvd`, `inv`, `solve`) in `mod.spl` with zero primitive types in signatures
- [ ] All specs (T-LAPACK-15, 16, 17) pass under `bin/simple test` with `SIMPLE_BLAS_BACKEND=mock`; zero `skip()`; zero `TODO→NOTE` conversions
- [ ] Mock structural invariants verified (non-negative singular values, orthogonal mock U/Vt shapes, 0-based Pivot.at assertions)
- [ ] `NotConverged` and `Singular` error paths covered by specs
- [ ] LAPACKE openblas path green on CPU-only CI (T-LAPACK-18)
- [ ] `doc/08_tracking/feature_request/scilib_perf_sugar.md` entries PERF-SUGAR-001, 003, 011 promoted from `anticipated` to `observed` or `fixed` before impl begins

---

## Anti-Patterns Explicitly Prohibited

1. **No nvfortran** — cuBLAS/cuSOLVER C API only (D-1)
2. **No `--mode=native` for slow specs** — all specs run interpreter mode; native-mode gives false greens (AC-7 / feedback_compile_mode_false_greens)
3. **No DataFrame ops** in any `linalg/` file — string-keyed indexing belongs in `std.df`
4. **No raw `i64` pivot arrays at Layer C** — `Pivot` wrapper required
5. **No raw `lwork: Index` at Layer C** — `Workspace<T>` query lifecycle is Layer B only
6. **No `skip()`** in any spec file — implement or delete (feedback_no_coverups)
7. **No TODO→NOTE conversions** — implement or file a concrete bug entry

---

## Perf-Sugar Cross-References

| Entry | Relevance to this area | Required status before impl |
|-------|------------------------|---------------------------|
| PERF-SUGAR-001 | `Workspace<T>` and `Pivot` allocation use typed buffer ctor | `fixed` (hard gate) |
| PERF-SUGAR-003 | `fn gesv<T>` generics erased in interp — workaround: `Float64`-specialized non-generic v1 signatures | `observed` + workaround plan |
| PERF-SUGAR-011 | `Float64(x)` wrapper-ctor overhead for eigenvalue/SVD output wrapping | `observed` + measurement |
| PERF-SUGAR-004 | Per-LAPACK-call FFI overhead — acceptable for matrix-level ops (BLAS level-3 equivalent); no batching needed in v1 | `anticipated` — do not over-optimize in v1 |
