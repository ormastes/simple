# Scilib Port Architecture

**Status:** Phase 3 complete (2026-04-27)  
**Scope:** `std.linalg` / `std.ndarray` / `std.df` / `std.ml` — full design, v1 impl = NDArray + linalg only  
**Supersedes:** nothing (greenfield namespaces); absorbs `src/lib/common/linear_algebra/` via rename  
**Locks:** OQ-A through OQ-F (see section 11)

---

## 1. Executive Summary

This document is the authoritative architecture for porting Fortran/CUDA Fortran scientific libraries (BLAS, LAPACK, cuBLAS, cuSOLVER) and Python scientific APIs (NumPy, pandas, scikit-learn) into Simple as Simple-native library surfaces. The port is constrained by five hard rules: no primitive types in any public API signature, math-block cooperation for linalg/ndarray expressions, naming harmony with existing `src/lib/`, CUDA Fortran first backend (via C API shim, not nvfortran), and explicit perf-sugar capture in `doc/08_tracking/feature_request/scilib_perf_sugar.md`. Full design covers four namespaces (`std.linalg`, `std.ndarray`, `std.df`, `std.ml`) and two backend tiers (cuBLAS/cuSOLVER with OpenBLAS fallback). Research Phase 2 (6 parallel agents, 2026-04-27) produced all input artifacts; this document synthesizes their convergent decisions plus six locked open-question resolutions.

The v1 deliverable is narrow by design. NDArray with broadcasting, slicing, shape/dtype/device, and pluggable storage backend; plus explicit `std.linalg` public API over eight BLAS/LAPACK kernels with a thin C/Rust shim layer. Math-block `@`/slice/method extensions land in v1 as runtime string-interp extensions (not HIR-lift). The existing `Tensor<T,N>` (libtorch-backed) is superseded by `NDArray<T>` with a backward `Tensor = NDArray` alias that expires at v1.1. PERF-SUGAR-001 (typed buffer ctor) is a hard gate before impl begins; PERF-SUGAR-011 (newtype zero-cost construction) is a soft prereq acknowledged by the no-primitive design.

Deferred to v1.1: `std.df` (DataFrame, Series) and `std.ml` shape (Estimator, Pipeline, preprocessing). Deferred to v2: cuDF/cuML (RAPIDS C++ ABI not stable for `extern C` binding), compiler-integrated math-block HIR-lift, and a pure-Simple backend for linalg. v1.1 targets 6–10 weeks after v1 ships; v2 is open-ended pending RAPIDS ABI stabilization and compiler maturity. The architecture is designed so each phase can advance independently: v1 impl agents need only sections 4–6; v1.1 agents need sections 8–9; v2 needs section 7's HIR-lift sketch.

---

## 2. Phased Rollout

### v1 — NDArray + linalg (target: 4–8 weeks)

**Scope:** `NDArray<T>` core; `std.linalg` public API; thin C/Rust shim (`libspl_cublas.so` / `libspl_lapack.so` / `libspl_cublas_mock.so`); math-block `@`, `:` slice, `.method` postfix, `inv`/`solve` arms as runtime extension; `Tensor = NDArray` backward alias.

**Acceptance gates (v1 → v1.1):**

1. PERF-SUGAR-001 landed (`rt_f64_array_alloc` extern; bootstrap-from-scratch rebuild complete).
2. `bin/simple test` passes all linalg+ndarray specs in interpreter mode with zero `skip()`.
3. `linalg.gemm`, `linalg.gesv`, `NDArray.zeros`, broadcasting, and sliced-view specs green.
4. `Tensor = NDArray` alias in place; `common/linear_algebra/` renamed to `common/linalg/`.
5. Eight PERF-SUGAR tracking entries promoted from `anticipated` to `observed` or `fixed`.

### v1.1 — DataFrame + sklearn shape (target: 6–10 weeks after v1)

**Scope:** `std.df` (`DataFrame`, `Series<T>`, CSV ingestion, column ops, groupby narrow path); `std.ml` (`Estimator` trait, `Transformer` trait, `Pipeline`, `StandardScaler`, `LinearRegression`, `KFold`, `metrics`); `std.ndarray` I/O (`save_npy`, `load_npy`, `load_txt`); strided-view support (PERF-SUGAR-005).

**Acceptance gates (v1.1 → v2):**

1. `bin/simple test` passes all df+ml specs interpreter-mode with zero `skip()`.
2. `df.groupby` narrow path (lazy `RowRange` iterator, no group materialization) green.
3. `ml.Pipeline` composes at least two `Transformer` + one `Estimator` in a test.
4. PERF-SUGAR-006 (symbol intern) addressed or explicitly deferred with rationale.

### v2 — cuDF/cuML + compiler-integrated math-block (open)

**Scope:** `std.df` cuDF backend (pending RAPIDS stable `extern C`); `std.ml` cuML subset; math-block HIR-lift (compile-time type-directed dispatch to cuBLAS kernels); pure-Simple backend for `std.linalg` (no shim); FMA sugar (PERF-SUGAR-008); loop fusion (PERF-SUGAR-013).

**Gate to start v2:** RAPIDS publishes a stable `extern "C"` surface for libcudf; compiler team commits to math-block HIR-lift work; PERF-SUGAR-001/002/003 all `fixed`.

---

## 3. No-Primitive Type System

All public API signatures use typed wrappers. Internal implementation may use primitives but must not expose them at any module boundary (function signature, struct field access, or return value). The no-primitive rule is enforceable by existing lint.

**Note on PERF-SUGAR-011:** `Float64(x)` allocates a heap object unless the compiler value-inlines single-field numeric wrappers (newtype optimization). PERF-SUGAR-011 is a soft prerequisite: the no-primitive design is correct, but is a "purity tax" at scale until the optimization lands. v1 impl agents must measure alloc cost for large array literal construction and escalate if it degrades test suite run time beyond 2× vs the primitive equivalent.

### Concrete Wrappers

| Wrapper | Definition shape | Location | FFI boundary rule |
|---------|-----------------|----------|-------------------|
| `Float64` | `struct Float64 { _v: f64 }` | `std.ndarray.types` | Layer A receives `f64`; Layer B wraps/unwraps |
| `Float32` | `struct Float32 { _v: f32 }` | `std.ndarray.types` | same |
| `Int64` | `struct Int64 { _v: i64 }` | `std.ndarray.types` | same |
| `Index` | `struct Index { _v: i64 }` | `std.ndarray.types` | cuBLAS `_64` API: `i64`; Layer B converts |
| `Shape` | `struct Shape { _dims: [Index] }` | `std.ndarray.types` | Layer B extracts `[i64]` for shim |
| `Stride` | `struct Stride { _vals: [Index] }` | `std.ndarray.types` | Layer B extracts `[i64]` for shim |
| `DType` | `enum DType { F16, F32, F64, I8, I16, I32, I64, U8, Bool, Complex64, Complex128 }` | **Re-export** from `tensor.spl` | no redefinition |
| `Device` | `enum Device { CPU, CUDA(index: Index) }` | **Re-export** from `tensor.spl` | no redefinition |
| `Scalar<T>` | `struct Scalar<T> { _v: T }` | `std.linalg.types` | zero-rank linalg result wrapper |
| `Matrix<T>` | `struct Matrix<T> { _inner: NDArray<T> }` | `std.linalg.types` | rank-2 assertion on construction |
| `Vector<T>` | `struct Vector<T> { _inner: NDArray<T> }` | `std.linalg.types` | rank-1 assertion on construction |

**Construction ergonomics:** Typed numeric literals (`2.718f64`) are available in Simple syntax. `Float64(x)` construction sugar should be a zero-cost wrapper. Free functions `f64(x)`, `idx(n)`, `shape(...)` may be provided as internal construction helpers that are not exported publicly — they return typed wrappers and are defined in `types.spl`.

**Conversion at FFI:** Layers A and B form the primitive/wrapper conversion boundary. Layer A is raw `extern fn` with primitives (`i64`, `f64`, `ptr-as-i64`). Layer B wraps primitives in typed wrappers for return values and unwraps typed wrappers to primitives for arguments. Layer C (public API) is primitive-free throughout.

---

## 4. `NDArray<T>` Design

`NDArray<T>` supersedes `Tensor<T,N>` (libtorch-backed). The rank parameter `N` is dropped from the public type signature (dynamic rank), keeping the API simpler. A backward alias `Tensor = NDArray` is in place for one release cycle (v1 only; removed at v1.1).

### Fields (internal)

```
struct NDArray<T>:
    _backend: StorageBackend   # trait object — cuBLAS / libtorch / mock
    _shape:   [Index]          # dynamic rank; owned
    _strides: [Stride]         # row-major strides computed on construction
    _dtype:   DType            # re-exported from tensor.spl
    _device:  Device           # re-exported from tensor.spl
    _offset:  Index            # byte offset into backing buffer (for views)
```

`StorageBackend` is a trait (no inheritance) implemented by:
- `CublasBackend` — wraps cuBLAS/cuSOLVER handle via `libspl_cublas.so`
- `LibtorchBackend` — wraps existing libtorch FFI from `tensor.spl`
- `MockBackend` — deterministic stub for interp-mode specs

### Broadcasting Algorithm

Broadcasting is the gating substrate for all NumPy-like operations. The algorithm is:

1. Right-align shapes: shorter shape is left-padded with `Index(1)`.
2. For each aligned dimension pair `(a, b)`: if `a == b`, output dim = `a`; if `a == Index(1)`, output dim = `b`; if `b == Index(1)`, output dim = `a`; else error (shape mismatch).
3. Result shape is the vector of output dims.

**Example:** `NDArray<Float64>` of shape `(3,1)` broadcast with `(1,4)` yields shape `(3,4)`. `NDArray.from_scalar(Float64(2.0))` (shape `()`) broadcasts with any shape.

Broadcasting runs in Layer B before dispatching to the backend. The backend always receives contiguous, non-broadcast buffers (the broadcast expansion is performed in the shim or via a `rt_ndarray_broadcast_expand` extern, not in the interpreter loop — per PERF-SUGAR-009 rationale).

### Slicing and Strided Views

- `NDArray[i, j]` — element access returning `T`; multi-axis, `Index`-typed.
- `NDArray[lo..hi, ..]` — slice returning `NDArray<T>` view (non-owning). The view shares the same `_backend` handle and `_offset`; strides are updated, no copy.
- `NDArray[.., j]` — column slice with stride `Shape._dims[0]`; returns strided view.
- Strided views are `O(1)`. Copy is only triggered by `.flatten()` or `.contiguous()`.

`Stride` carries non-unit values for transposed or sliced views. Layer B computes strides from shape on any reshape/transpose. The shim receives `(ptr, shape, strides, offset)` so it can apply the stride layout. Strided-view support for the interpreter is tracked as PERF-SUGAR-005 (P1, not blocking v1 but must land before v1.1 column ops).

### DType Dispatch

Operations dispatch on `_dtype` at Layer B:
- `DType.F64` → `rt_blas_dgemm` (double precision)
- `DType.F32` → `rt_blas_sgemm` (single precision)
- `DType.I64` / `DType.I32` → fallback to pure-Simple loops (no BLAS for integer arrays)

Unsupported dtype + operation combinations return `Result.Err(UnsupportedDType)` — no silent fallback.

### Supersede and Alias Plan

- `Tensor<T,N>` in `nogc_sync_mut/src/tensor.spl` is renamed `NDArray<T>` (rank becomes dynamic).
- `type Tensor<T> = NDArray<T>` alias added in same file.
- Alias is marked `#[deprecated(since="v1.1")]`.
- `DType` and `Device` enums are unchanged; they remain in `tensor.spl` and are re-exported by `std.ndarray`.
- The existing libtorch backend becomes `LibtorchBackend` implementing `StorageBackend`.

---

## 5. `std.linalg` Public API

Physical location: `src/lib/common/linalg/` (renamed from `common/linear_algebra/`).  
Import: `use std.linalg`.  
Tier: `common/` — pure math, no async, no GC.

**Row-major external contract:** All public functions accept and return row-major `NDArray<T>`. Column-major conversion for cuBLAS happens in Layer B (operand swap via `(AB)ᵀ = BᵀAᵀ`). Callers never see column-major layout.

### Concrete Signatures

| Function | Signature | BLAS/LAPACK kernel | Notes |
|----------|-----------|-------------------|-------|
| `axpy` | `fn axpy(alpha: Float64, x: NDArray<Float64>, y: NDArray<Float64>) -> NDArray<Float64>` | BLAS daxpy | `y = alpha*x + y` |
| `gemv` | `fn gemv(alpha: Float64, a: Matrix<Float64>, x: Vector<Float64>, beta: Float64, y: Vector<Float64>) -> Vector<Float64>` | BLAS dgemv | `y = alpha*A*x + beta*y` |
| `gemm` | `fn gemm(alpha: Float64, a: Matrix<Float64>, b: Matrix<Float64>, beta: Float64, c: Matrix<Float64>) -> Matrix<Float64>` | BLAS dgemm | `C = alpha*A*B + beta*C` |
| `dot` | `fn dot(x: Vector<Float64>, y: Vector<Float64>) -> Float64` | BLAS ddot | inner product |
| `norm` | `fn norm(x: NDArray<Float64>, ord: NormOrd) -> Float64` | BLAS dnrm2 | `NormOrd` enum: `L1, L2, Inf` |
| `gesv` | `fn gesv(a: Matrix<Float64>, b: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>` | LAPACK dgesv | solve `AX=B`; hides pivot array |
| `getrf` | `fn getrf(a: Matrix<Float64>) -> Result<(Matrix<Float64>, NDArray<Index>), LinalgError>` | LAPACK dgetrf | LU factorization; returns `(LU, ipiv)` |
| `geqrf` | `fn geqrf(a: Matrix<Float64>) -> Result<(Matrix<Float64>, Vector<Float64>), LinalgError>` | LAPACK dgeqrf | QR; returns `(QR, tau)` |
| `syevd` | `fn syevd(a: Matrix<Float64>) -> Result<(Vector<Float64>, Matrix<Float64>), LinalgError>` | LAPACK dsyevd | eigenvalues `(vals, vecs)` for symmetric A |
| `gesvd` | `fn gesvd(a: Matrix<Float64>) -> Result<(Matrix<Float64>, Vector<Float64>, Matrix<Float64>), LinalgError>` | LAPACK dgesvd | SVD `(U, s, Vt)` |
| `inv` | `fn inv(a: Matrix<Float64>) -> Result<Matrix<Float64>, LinalgError>` | LAPACK dgetrf+dgetri | matrix inverse |
| `solve` | `fn solve(a: Matrix<Float64>, b: Vector<Float64>) -> Result<Vector<Float64>, LinalgError>` | LAPACK dgesv | vector solve |

**Free functions vs methods:** All linalg operations are free functions in `std.linalg`. Reductions (`sum`, `mean`, `norm`) on `NDArray` are *methods* on `NDArray<T>`, never free functions, to avoid shadowing `std.math` scalar helpers at import scope.

**Error type:** `LinalgError` is an enum with variants `Singular`, `NotConverged(Index)`, `DimensionMismatch(Shape, Shape)`, `UnsupportedDType(DType)`. It is defined in `std.linalg.types`.

---

## 6. FFI Shim Layer

### Three-Layer Stack

| Layer | File | Role |
|-------|------|------|
| A — raw extern | `linalg/ffi_blas.spl` | `extern fn rt_blas_dgemm(handle: i64, m: i64, n: i64, k: i64, alpha: f64, a_ptr: i64, lda: i64, b_ptr: i64, ldb: i64, beta: f64, c_ptr: i64, ldc: i64) -> i64` |
| B — SFFI wrapper | `linalg/blas.spl` | converts `Float64`/`Matrix<Float64>`/`Index` ↔ raw; applies `(AB)ᵀ=BᵀAᵀ` operand swap; manages handle lifecycle |
| C — public API | `linalg/mod.spl` | `linalg.gemm(...)` — no primitives visible |

### Shared Libraries

| Library | File | Backend | Symbols |
|---------|------|---------|---------|
| `libspl_cublas.so` | `src/runtime/scilib/cublas_shim.c` | cuBLAS + cuSOLVER (CUDA backend) | `rt_blas_handle_create`, `rt_blas_dgemm`, `rt_lapack_dgesv`, `rt_cuda_malloc`, `rt_cuda_free`, `rt_cuda_memcpy_htod`, `rt_cuda_memcpy_dtoh` |
| `libspl_openblas.so` | `src/runtime/scilib/openblas_shim.c` | OpenBLAS / Netlib LAPACKE (host fallback) | same symbol set as cublas shim; device-pointer args = host pointers |
| `libspl_cublas_mock.so` | `src/runtime/scilib/mock_shim.c` | Deterministic stub for interp-mode | all symbols present; compute functions return deterministic dummy values (zeros/identity); `rt_blas_handle_create` returns `i64(1)` |

### Symbol Naming Convention

- Runtime symbols: `rt_blas_<level>_<function>` (e.g. `rt_blas_dgemm`, `rt_blas_ddot`)
- LAPACK symbols: `rt_lapack_<function>` (e.g. `rt_lapack_dgesv`, `rt_lapack_dgesvd`)
- CUDA memory: `rt_cuda_malloc(bytes: i64) -> i64`, `rt_cuda_free(ptr: i64)`, `rt_cuda_memcpy_htod(dst: i64, src: i64, bytes: i64)`, `rt_cuda_memcpy_dtoh(dst: i64, src: i64, bytes: i64)`
- Use 64-bit integer interface exclusively (`cublasDgemm_64` / CUDA ≥ 11.7). Older CUDA: Layer B applies `Index → i32` clamping guarded by `rt_cuda_api_version() -> i64`.

### Backend Selection

Environment variable `SIMPLE_BLAS_BACKEND`:

| Value | Loaded library | Fallback |
|-------|---------------|---------|
| `cublas` | `libspl_cublas.so` | error if not found |
| `openblas` | `libspl_openblas.so` | error if not found |
| `mock` | `libspl_cublas_mock.so` | always available |
| (unset) | tries `cublas`, then `openblas`, then `mock` | — |

Selection happens at `BlasHandle.create()` time. The handle is stored in a module-level singleton; handle is per-thread when `Device.CUDA` is active (per NVIDIA recommendation). Thread-safety interacts with `nogc_async_mut/` actors; the handle must not be shared across actor boundaries without explicit lock.

### Interp-Mode AC-7 Compliance

`spl_dlopen` is not whitelisted in interpreter mode. Resolution:

- `libspl_cublas_mock.so` is placed in `$SIMPLE_SFFI_PATH` by default in the test harness.
- `SIMPLE_BLAS_BACKEND=mock` is set in `bin/simple test` when running `linalg/` specs.
- All linalg specs pass under interpreter mode using the mock backend.
- Specs that require real GPU results are annotated `#[gpu_only]` and excluded from `bin/simple test`; they run in a separate CI stage with `SIMPLE_BLAS_BACKEND=cublas`.

### Future Pure-Simple Backend Slot

`StorageBackend` trait includes a `pure_simple` variant slot reserved for a future hand-written Simple linalg implementation (no shim). When this backend is registered, `SIMPLE_BLAS_BACKEND=pure_simple` selects it. This slot enables the gradual migration path from FFI-backed to self-hosted.

---

## 7. `math{}` Block Contract

### v1 Additions (runtime string-interp only)

The `math{}` block remains a string-payload runtime interpreter in v1. OQ-A locks this decision (HIR-lift deferred to v2). New token/AST additions required for v1:

| Addition | Location | Change |
|----------|----------|--------|
| `@` infix token | `blocks/math/lexer.rs` | `MathToken::At`; precedence between `Mul` and `Pow` |
| `:` slice token | `blocks/math/lexer.rs` | `MathToken::Colon`; free (math lexer uses `..` for Range) |
| `MatMul(lhs, rhs)` AST variant | `blocks/math/ast.rs` | dispatched to `Tensor::matmul` in eval |
| `Slice { base, ranges: [SliceRange] }` | `blocks/math/ast.rs` | `SliceRange = { start: Option<MathExpr>, stop: Option<MathExpr> }` |
| `.method(args)` parse | `blocks/math/parser.rs` | normalised at parse-time to `App("method", [receiver] ++ args)`; avoids a `MethodCall` AST node in v1 |
| `App("inv", [A])` arm | `blocks/math/eval/mod.rs` | dispatches to `eval_inv`; FFI to `rt_lapack_dgetrf`+`rt_lapack_dgetri` |
| `App("solve", [A, b])` arm | `blocks/math/eval/mod.rs` | dispatches to `eval_solve`; FFI to `rt_lapack_dgesv` |
| `App("sum", [A, axis])` | `blocks/math/eval/mod.rs` | extends existing `eval_sum_tensor` to accept optional axis integer |
| `App("mean", [A, axis])` | same | same pattern |

**PERF-SUGAR-002 note:** v1 math-block lowering allocates one intermediate `Block` per operator. For `math { A @ B + v }` this is two intermediate allocations. This is known and accepted for v1; PERF-SUGAR-002 (kernel fusion) is the v2 fix. Teams must not use `math{}` in hot inner loops in v1 — use explicit `linalg.gemm` calls instead.

### v2 Path to Compile-Time HIR-Lift (sketch only)

When the compiler team commits to HIR-lift, the migration path is:

1. Add `math{}` as a grammar node in the Simple parser (not just a string-payload block), capturing the enclosed expression as an HIR sub-tree.
2. Resolve variable types in the HIR sub-tree using the surrounding scope's type environment.
3. At codegen: if all operands are statically typed `NDArray<Float64>`, emit `linalg.gemm` / `rt_blas_dgemm` directly. If types are dynamic, fall back to the v1 runtime evaluator.
4. This requires a `TypeAnnotatedMathExpr` IR sitting between the parser and the codegen — the existing `MathExpr` AST becomes the fallback path, not the primary.

No compiler changes are made in v1 toward this path. The v2 sketch is informational only.

---

## 8. `std.df` — DataFrame Design (v1.1 scope)

Physical location: `src/lib/nogc_sync_mut/df/`.  
Import: `use std.df`.  
Tier: `nogc_sync_mut/` — synchronous I/O, FFI, mutable state; no GC needed.

`std.df` is explicitly excluded from math-block integration. String-keyed indexing, groupby aggregators, and join operations do not fit `MathExpr`. Use plain Simple method calls.

### Core Types

```
struct Series<T>:
    _name:   Symbol           # interned column name (PERF-SUGAR-006)
    _data:   NDArray<T>       # backing array; dtype from T
    _index:  NDArray<Index>   # row labels (integer by default)

struct DataFrame:
    _schema: [Symbol]         # column names in order
    _cols:   [SeriesErased]   # type-erased column array
    _index:  NDArray<Index>   # shared row index

enum SeriesErased:
    F64Series(Series<Float64>)
    I64Series(Series<Int64>)
    TextSeries(Series<text>)
    BoolSeries(Series<Bool>)
```

**Symbol type:** `Symbol` is an interned `text` backed by `rt_intern_symbol(str: text) -> i64`. Column equality checks use `Symbol` pointer comparison (`O(1)`). This is a soft dependency on PERF-SUGAR-006; until `rt_intern_symbol` is available, `Symbol = text` with `O(len)` equality is the fallback — flagged in the tracking file.

### Indexing

| Operation | Signature | Return |
|-----------|-----------|--------|
| Column select | `df[col: Symbol] -> SeriesErased` | single column |
| Multi-column | `df.select(cols: [Symbol]) -> DataFrame` | projection |
| Row filter | `df.filter(mask: NDArray<Bool>) -> DataFrame` | boolean mask |
| Positional | `df.iloc(row: Index, col: Index) -> Value` | scalar |
| Label | `df.loc(row: Index, col: Symbol) -> Value` | scalar |

### Broadcast Scalar Ops

Scalar operations on `Series<T>` are methods, never free functions:

```
fn Series<T>.add_scalar(rhs: T) -> Series<T>
fn Series<T>.mul_scalar(rhs: T) -> Series<T>
```

Operator overloading (`+`, `*`) with `T`-typed RHS calls these methods.

### Groupby (narrow path only)

GroupBy uses a lazy `RowRange` iterator — no group materialization:

```
struct RowRange:
    key:   Value
    start: Index
    stop:  Index

fn DataFrame.groupby(col: Symbol) -> GroupBy
fn GroupBy.sum()  -> DataFrame
fn GroupBy.mean() -> DataFrame
fn GroupBy.agg(f: fn(NDArray<Float64>) -> Float64) -> DataFrame
```

Full materialized groups are never produced by default. Aggregation runs on range-backed column views (`StridedView`, PERF-SUGAR-005 — v1.1 gate).

### I/O

Compose `std.common.csv` — no reimplementation:

```
fn DataFrame.from_csv(path: text, sep: text, header: Bool) -> Result<DataFrame, IoError>
fn DataFrame.to_csv(path: text, sep: text) -> Result<Unit, IoError>
fn DataFrame.from_ndarray(arr: NDArray<Float64>, cols: [Symbol]) -> DataFrame
```

Parquet: deferred to v2 (requires a new FFI against `libparquet`).

---

## 9. `std.ml` Design (v1.1 scope)

Physical location: `src/lib/gc_async_mut/ml/`.  
Import: `use std.ml`.  
Tier: `gc_async_mut/` — model state is GC-backed; training loops are async.  
Re-exports `nn/loss`, `nn/norm` from `common/pure/nn/` — does not redefine.  
cuML deferred to v2.

### Estimator and Transformer Traits

No inheritance. Composition only. Traits are the extension mechanism:

```
trait Estimator:
    fn fit(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Unit, MlError>
    fn predict(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
    fn score(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Float64, MlError>

trait Transformer:
    fn fit(self, x: NDArray<Float64>) -> Result<Unit, MlError>
    fn transform(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
    fn fit_transform(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
```

`fit_transform` has a default implementation: `self.fit(x)?; self.transform(x)`.

### Pipeline

Pipeline is a tuple-of-steps, not a dynamic list — each step type is preserved:

```
struct Pipeline<Steps>:
    _steps: Steps   # tuple type, e.g. (StandardScaler, LinearRegression)

fn Pipeline.new(steps: Steps) -> Pipeline<Steps>
fn Pipeline.fit(self, x: NDArray<Float64>, y: NDArray<Float64>) -> Result<Unit, MlError>
fn Pipeline.predict(self, x: NDArray<Float64>) -> Result<NDArray<Float64>, MlError>
```

Tuple-of-steps avoids the "clone semantics" problem (no `dyn Estimator` heap boxing). Each step implements either `Transformer` or `Estimator`; the pipeline applies transformers in sequence then calls the final estimator. Generic dispatch limitations (PERF-SUGAR-003) affect `Pipeline<Steps>` in interpreter mode — until monomorphization lands, v1.1 may need hand-specialized pipeline types for common combos.

### v1.1 Models and Preprocessing

| Type | Trait | Notes |
|------|-------|-------|
| `StandardScaler` | `Transformer` | stateful `mean_/std_` per feature column |
| `MinMaxScaler` | `Transformer` | stateful `min_/max_` per feature |
| `LabelEncoder` | `Transformer` | sorted labels → `Index`; `inverse_transform` method |
| `LinearRegression` | `Estimator` | LAPACK DGELS / normal equation |
| `Ridge` | `Estimator` | closed-form `(XᵀX + αI)⁻¹Xᵀy` via `linalg.gesv` |
| `KFold` | — | index-pair iterator; `n_splits: Index`, `shuffle: Bool` |
| `metrics` | — | `mse`, `accuracy<T>`, `r2` as free functions in `std.ml.metrics` |

`std.ml` re-exports existing `nn/loss.spl` and `nn/norm.spl` without redefining. `Device` is re-exported from `std.ndarray` (which re-exports from `tensor.spl`).

---

## 10. Perf-Sugar Dependencies

| Phase | Gating item | Status required | Risk if missed |
|-------|-------------|----------------|----------------|
| Before NDArray impl (v1) | PERF-SUGAR-001 (typed buffer ctor) | `fixed` | every spec times out; no array > few hundred elements in interp |
| Before NDArray impl (v1) | PERF-SUGAR-011 (newtype zero-cost) | `observed` + workaround plan | no-primitive rule is heap-alloc tax at 1M-elem scale |
| During linalg spec (v1) | PERF-SUGAR-003 (generic erased dispatch) | `observed` + workaround plan | `NDArray<T>` / `fn dot<T>` unusably slow in interp-mode |
| During math-block spec (v1) | PERF-SUGAR-002 (math{} intermediate alloc) | `anticipated` — do not use math{} in hot loops | math-block slower than explicit extern calls |
| Before df impl (v1.1) | PERF-SUGAR-005 (strided view) | `fixed` | all column ops are O(n) copy; groupby broken |
| Before df impl (v1.1) | PERF-SUGAR-006 (symbol intern) | `fixed` or fallback plan | column-name ops O(len) vs O(1) |
| Before groupby spec (v1.1) | PERF-SUGAR-007 (lazy groupby) | design decision — lazy RowRange from day one | 1000 group materializations for 10M-row df |
| v2 math-block HIR-lift | PERF-SUGAR-002 (kernel fusion) | `fixed` | math-block cannot outperform explicit externs |
| v2 pure-Simple backend | PERF-SUGAR-008 (FMA sugar) | `fixed` | pure-Simple linalg 2× slower than BLAS for float-heavy code |
| v2 pure-Simple backend | PERF-SUGAR-013 (loop fusion / SIMD) | `fixed` | element-wise loops 2–8× slower than NumPy |

**PERF-SUGAR-001 is a hard gate.** No NDArray impl work begins until `rt_f64_array_alloc` (and siblings `rt_f32_array_alloc`, `rt_i64_array_alloc`) are landed and a bootstrap rebuild (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`) is complete. This is non-negotiable per the `feedback_extern_bootstrap_rebuild` constraint.

---

## 11. Open Questions Resolved

**OQ-A (math-block dispatch model):** v1 = extend runtime `math{}` string-interp. Compile-time HIR-lift deferred to v2. Rationale: HIR-lift requires rebuilding `math{}` as a proper grammar node with type-environment access — a major compiler project with no existing precedent. The runtime-probe model (check `MathValue::Tensor` dtype at eval time, dispatch to cuBLAS) extends the existing `backend/auto_select.rs` hook point and delivers 90% of the user-visible benefit with 10% of the risk.

**OQ-B (existing Tensor<T,N>):** Supersede with `NDArray<T>` + pluggable `StorageBackend` trait. Libtorch backend becomes `LibtorchBackend`. Backward alias `type Tensor<T> = NDArray<T>` in `tensor.spl` for one release cycle (v1), marked deprecated, removed at v1.1. Rationale: two coexisting types (`Tensor` + `NDArray`) with different storage would fracture the stdlib and confuse users about which to use. The pluggable-backend design preserves libtorch functionality for existing code while enabling cuBLAS and mock backends without duplication.

**OQ-C (BLAS row-major vs column-major):** Row-major external API, column-major internal via `(AB)ᵀ = BᵀAᵀ` operand-swap at FFI boundary. Rationale: Simple users expect row-major (C-like) layout. cuBLAS is always column-major. The operand-swap is a standard idiom (`cublasDgemm` with both ops set to `CUBLAS_OP_T`, operands swapped B/A). Layer B applies this transparently; the public API is row-major throughout, no exceptions.

**OQ-D (interp dlopen):** Mock `libspl_cublas_mock.so` for interp-mode tests; native-mode for real backend. Rationale: `spl_dlopen` is not whitelisted in interpreter mode (R-3 risk). Mock shim provides deterministic dummy returns for all BLAS/LAPACK symbols, placed in `$SIMPLE_SFFI_PATH` by default. Specs run entirely in interpreter mode satisfying AC-7. GPU specs annotated `#[gpu_only]` run in a separate CI stage.

**OQ-E (Codex scope cut):** Path B — full design covers all four namespaces; v1 impl ships NDArray + linalg only. Rationale: Codex correctly identifies that math-block + CUDA Fortran-first backend turns a library port into a compiler+toolchain project. The scope cut to NDArray+linalg first produces a real user-facing deliverable in 4–8 weeks. The full design is preserved so v1.1 agents have a complete spec rather than a moving target.

**OQ-F (PERF-SUGAR-001 gating):** PERF-SUGAR-001 must land before Phase 5 NDArray impl. The analogous `rt_bytes_alloc` fix (feedback_interpreter_bulk_buffer) transformed `[u8]` buffer construction from "never completes" to 1.5 s. Without `rt_f64_array_alloc`, every `NDArray.zeros(Shape(1024, 1024))` call will not complete in interpreter mode. Working around this with `rt_bytes_alloc` + reinterpret-cast is a cover-up violating `feedback_no_coverups`. Rationale: PERF-SUGAR-002/003 are watchful (observe and plan mitigation) but not hard gates; PERF-SUGAR-001 is categorically blocking.

---

## 12. Acceptance Gates Between Phases

### v1 → v1.1

All of the following must be green:

- [ ] `PERF-SUGAR-001` status = `fixed`; bootstrap rebuild complete
- [ ] `bin/simple test src/lib/common/linalg/` passes; zero `skip()`, zero TODO→NOTE
- [ ] `bin/simple test src/lib/nogc_sync_mut/ndarray/` passes; zero `skip()`
- [ ] `linalg.gemm`, `linalg.gesv`, `linalg.gesvd`, `linalg.syevd` specs green in interpreter mode with mock backend
- [ ] `NDArray.zeros`, `NDArray.ones`, `NDArray.from_seq`, broadcast add, row/column slice specs green
- [ ] `common/linear_algebra/` directory renamed to `common/linalg/`; no file removed
- [ ] `Tensor = NDArray` alias in place; `#[deprecated(since="v1.1")]` annotation present
- [ ] `DType`/`Device` re-exported from `std.ndarray`; no redefinition anywhere
- [ ] Zero primitive type leaks in any public `std.linalg` or `std.ndarray` signature
- [ ] `SIMPLE_BLAS_BACKEND=mock` default confirmed in test harness
- [ ] `doc/08_tracking/feature_request/scilib_perf_sugar.md` updated: at least PERF-SUGAR-001/003/011 promoted from `anticipated` to `observed` or `fixed`

### v1.1 → v2

All of the following must be green:

- [ ] `bin/simple test src/lib/nogc_sync_mut/df/` passes; zero `skip()`
- [ ] `bin/simple test src/lib/gc_async_mut/ml/` passes; zero `skip()`
- [ ] `DataFrame.from_csv`, `DataFrame.groupby(...).sum()` (lazy RowRange path), `df.filter`, `df.select` specs green
- [ ] `Pipeline` with `StandardScaler` + `LinearRegression` end-to-end spec green
- [ ] `PERF-SUGAR-005` (strided view) status = `fixed`
- [ ] `PERF-SUGAR-006` (symbol intern) status = `fixed` or formal deferral with fallback documented
- [ ] `Tensor = NDArray` alias removed; no remaining references to `Tensor` type in `src/lib/`
- [ ] cuDF/cuML deferral confirmed in writing (RAPIDS ABI status checked); no v2 code written speculatively

---

## 13. TODO INDEX — Phase 4 Agent Task Files

Eight task files to be written under `doc/03_plan/agent_tasks/scilib_port_*.md`. Dependency order determines sequencing for parallel agents. No two agents sharing a dependency may run in parallel against the same file.

**Dependency graph (linearized):**

```
perf_sugar → ndarray → blas + lapack (parallel) → cuda_fortran → math_block → df → ml
```

| File | Scope blurb | Dependencies |
|------|-------------|-------------|
| `scilib_port_perf_sugar.md` | Land `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc` externs; bootstrap rebuild; promote PERF-SUGAR-001/011/003 to `observed`; plan mitigation for each P0 wedge before ndarray impl begins. All tasks ≤ 2-day granularity. | None — must complete before all others |
| `scilib_port_ndarray.md` | Design and implement `NDArray<T>` struct, `StorageBackend` trait, `Shape`/`Stride`/`Index`/`Float64`/`Float32`/`Int64` wrappers, factory methods (`zeros`, `ones`, `from_seq`, `linspace`, `arange`), broadcasting engine, sliced/strided views, dtype dispatch, `Tensor = NDArray` alias, `DType`/`Device` re-exports. Specs first. | `perf_sugar` (PERF-SUGAR-001 fixed) |
| `scilib_port_blas.md` | Layer A/B/C for BLAS subset: `axpy`, `dot`, `nrm2`, `gemv`, `gemm`, `scal`. Write Layer A `extern fn` decls, Layer B operand-swap wrapper, Layer C public API. Write mock shim symbols. Specs run under `SIMPLE_BLAS_BACKEND=mock`. | `ndarray` |
| `scilib_port_lapack.md` | Layer A/B/C for LAPACK subset: `gesv`, `getrf`, `geqrf`, `syevd`, `gesvd`, `getri`. `LinalgError` enum. Workspace buffer allocation pattern (query-then-compute). Error handling (`devInfo` → `LinalgError`). | `ndarray` |
| `scilib_port_cuda_fortran.md` | Build `libspl_cublas.so` and `libspl_lapack.so` C/Rust shim crates. cuBLAS `_64` API binding for each BLAS symbol. cuSOLVER binding for each LAPACK symbol. `SIMPLE_BLAS_BACKEND` env-var selection logic. Host-pointer fallback in `libspl_openblas.so`. Mock shim `libspl_cublas_mock.so`. GPU CI stage setup. | `blas`, `lapack` (shim implements their symbols) |
| `scilib_port_math_block.md` | Compiler changes: add `@` token, `:` slice token, `MatMul` AST variant, `Slice` AST node, `.method` postfix parse normalisation. Eval: `inv`/`solve` arms with LAPACK FFI calls, axis-parameterised `sum`/`mean`. Rendering updates. Specs for `math { A @ B + v }` and `math { A[1:3, ..] }`. PERF-SUGAR-002 observed + workaround documented. | `ndarray`, `blas`, `lapack` |
| `scilib_port_df.md` | `DataFrame`, `Series<T>`, `Symbol` (interned), `SeriesErased` enum. Factory: `from_csv` (compose `std.common.csv`), `from_ndarray`. Ops: `select`, `filter`, `iloc`, `loc`, `assign`, `drop`, `rename`, `sort_values`. Groupby lazy RowRange. `drop_na`, `fill_na`. `to_csv`. PERF-SUGAR-005/006/007 observed before impl. | `ndarray` (columns backed by `NDArray<T>`) |
| `scilib_port_ml.md` | `Estimator` and `Transformer` traits. `Pipeline<Steps>`. `StandardScaler`, `MinMaxScaler`, `LabelEncoder`, `LinearRegression`, `Ridge`, `KFold`. `metrics` module (`mse`, `accuracy<T>`, `r2`). Re-export `nn/loss`, `nn/norm`. PERF-SUGAR-003 workaround for Pipeline in interp mode. | `ndarray`, `df` (for DataLoader) |

**Parallel-safety rule:** `blas.md` and `lapack.md` agents may run in parallel (disjoint files: `linalg/ffi_blas.spl` vs `linalg/ffi_lapack.spl`). All other pairs are sequential per the dependency graph. No two agents touch the same `.spl` file simultaneously — per `feedback_parallel_scope_partition`.
