# Naming Harmony Audit — std.linalg / std.ndarray / std.df / std.ml

**Date:** 2026-04-27  
**Scope:** Conflict/reuse analysis against existing `src/lib/` for four proposed namespaces.  
**Sibling scopes (do not touch):** Fortran/CUDA ABI, Python inventory, math-block lowering, perf-sugar, Codex risk.

---

## 1. Existing Modules Inventory

### 1.1 Linear Algebra (already present)

`src/lib/common/linear_algebra/` is the primary conflict zone:

| File | Content |
|------|---------|
| `types.spl` | Core type definitions and constants |
| `matrix_ops.spl` | Matrix operations (add, mul, scalar ops) |
| `matrix_ops_linalg.spl` | LAPACK-style ops (solve, inv, det) |
| `vector_ops.spl` | Dot product, cross product, norms |
| `decomposition.spl` | LU, QR, Cholesky decompositions |
| `eigenvalues.spl` | Eigenvalue/eigenvector routines |
| `solve.spl` | Linear system solving |
| `utilities.spl` | Helpers |

Also: `src/lib/common/engine/math2d.spl`, `math3d.spl`, `math3d/` subtree (vec, mat, quat, transform).

### 1.2 Tensor (already present, cross-cutting)

`src/lib/nogc_sync_mut/src/tensor.spl` — a substantial `Tensor<T, N>` struct (backed by PyTorch-style handles) with:
- `sum`, `mean`, `std`, `variance`, `norm`, `min`, `max`, `prod` (scalar and axis-reduced)
- `transpose`, `permute`, `reshape`, `view`, `flatten`, `squeeze`, `unsqueeze`
- `abs`, `sqrt`, `log`, `log2`, `log10`, `sin`, `cos`, `sinh`, `cosh`
- `argmin`, `argmax`, `cumsum`, `cumprod`
- `DType` enum (F32/F64/I32/I64/...), `Device` struct (cpu/cuda)
- Also: `src/lib/nogc_sync_mut/src/tensor/` subtree with factory.spl, ops subdirs.

### 1.3 Math

`src/lib/common/math.spl` — scalar functions with `math_` prefix convention:
`math_abs`, `math_min`, `math_max`, `math_clamp`, `math_sign`, `math_lerp`, `math_gcd`, `math_lcm`, `math_pow_i64`, `math_factorial`, `sum_i64`, `product_i64`, `average_i64`, `median_i64`.  
Also convenience aliases: `abs_i64`, `min_i64`, `max_i64`, etc. (unqualified).

`src/lib/common/matrix_utils.spl` — additional matrix helpers.  
`src/lib/common/math3d/math_util.spl`, `src/lib/common/engine/math2d.spl`.  
`src/lib/nogc_sync_mut/src/math/` subtree, `src/lib/nogc_sync_mut/io/math.spl`.

### 1.4 Statistics / Numerical Methods

`src/lib/common/statistics/` — `descriptive.spl`, `distributions.spl`, `inference.spl`, `correlation.spl`.  
`src/lib/common/stats_utils.spl` — standalone stats helpers.  
`src/lib/common/numerical_methods/` — `curve_fitting.spl`, `differentiation.spl`, `eigenvalues.spl`, `integration.spl`, `ode.spl`, `optimization.spl`.  
`src/lib/common/b_tree/statistics.spl`, `src/lib/nogc_sync_mut/benchmark/stats.spl`, `benchmark_stats.spl`.

### 1.5 FFT

`src/lib/common/fft/` — `dft.spl`, `fft.spl`, `ifft.spl`, `conv.spl`, `types.spl`.

### 1.6 Random

`src/lib/common/random_utils.spl`, `src/lib/common/rsa/random.spl`, `src/lib/common/secure_random/`.  
`src/lib/nogc_sync_mut/src/core/random.spl`.

### 1.7 ML (already present)

`src/lib/nogc_async_mut/ml/` — `async_training.spl`, `data_pipeline.spl`, `mod.spl`.  
`src/lib/nogc_sync_mut/torch/` — `backend.spl`, `dyn_ffi.spl`, `ffi.spl`.  
`src/lib/common/pure/nn/` — `loss.spl`, `norm.spl`, `pooling.spl`, `serialization.spl`.  
`src/lib/common/torch/dyn_ffi_tensor_ops.spl`.

### 1.8 Data / Serialization

`src/lib/common/csv/` — `parse.spl`, `serialize.spl`, `transform.spl`, `types.spl`.  
`src/lib/common/encoding/`, `encoding.spl`, `encoding_base.spl` — UTF-8/16/32, text_ops.  
`src/lib/common/text.spl`, `text_advanced.spl`.  
No parquet module found. No DataFrame module found.

### 1.9 Units

`src/lib/common/engine/units.spl` — game/physics engine units (not SI dimensional analysis).

---

## 2. Conflicts Found

### 2.1 std.linalg — SEVERE conflicts

The proposed `std.linalg` namespace collides directly with `src/lib/common/linear_algebra/`. That module already has:
- `decomposition`, `eigenvalues`, `solve`, `matrix_ops`, `vector_ops`, `types`, `utilities`

**Conflict list:**
1. `dot` — present in `vector_ops.spl`
2. `norm` — present in `vector_ops.spl` and `Tensor.norm()`
3. `transpose` — present in `Tensor.transpose()` and `matrix_ops.spl`
4. `solve` — `linear_algebra/solve.spl` top-level module name
5. `decomposition` — `linear_algebra/decomposition.spl` top-level module name
6. `eigenvalues` — `linear_algebra/eigenvalues.spl` and `numerical_methods/eigenvalues.spl`
7. `matrix_utils` — `src/lib/common/matrix_utils.spl` at top level of common

**Recommendation:** `std.linalg` must be the authoritative namespace. `common/linear_algebra/` lives at the `common/` tier (pure functions, no I/O); `std.linalg` should also live at `common/linalg/` (not `nogc_sync_mut/`) to match tier. The existing `common/linear_algebra/` is renamed `common/linalg/` and its existing files become the private implementation layer that `std.linalg` re-exports. Do not duplicate.

### 2.2 std.ndarray — MODERATE conflicts

`Tensor<T, N>` in `nogc_sync_mut/src/tensor.spl` is already an N-dimensional array type covering almost the entire NumPy surface:
- `sum`, `mean`, `min`, `max`, `std`, `norm` — all present as methods
- `reshape`, `view`, `flatten`, `squeeze`, `unsqueeze` — all present
- `DType` enum — present (F32, F64, I32, I64)
- `Device` struct — present

**Storage backend note:** `tensor.spl` states it is "Backed by PyTorch tensors" (a libtorch FFI). The scilib project's locked v1 backend is CUDA Fortran / cuBLAS, not libtorch. These are different storage runtimes. Two options:

- **Option A (rename):** Rename `Tensor<T,N>` to `NDArray<T,N>`, make storage pluggable via a `StorageBackend` trait (libtorch backend + CUDA-Fortran backend both conform). Preferred if libtorch coupling is acceptable for non-scilib consumers.
- **Option B (new type):** Keep `Tensor<T,N>` as the libtorch-backed type; introduce `NDArray<T,N>` as a separate CUDA-Fortran-backed type at the scilib layer; they share the `DType`/`Device` types but differ in storage.

**Decision deferred to architecture phase.** This document records the conflict; arch must pick. Either way, do not duplicate `DType`, `Device`, or the elementwise method surface.

**Conflicts:**
1. `Tensor` vs `NDArray` — same concept, different names; two implementations would fracture the stdlib.
2. `DType` — already defined in `tensor.spl`; re-defining in `std.ndarray` would shadow.
3. `sum`, `mean`, `min`, `max`, `norm` — these are Tensor *methods*; `std.ndarray` should expose them only as methods on `NDArray`, never as free functions, to avoid shadowing `std.math` scalar helpers at import scope. **Rule: reduction operations on arrays are methods; free functions in this scope are reserved for `std.math` scalars.**
4. `norm` — exists in both `Tensor` methods and `common/linear_algebra/vector_ops.spl` as a free function; the free-function form must be removed from or kept private to `common/linalg/`.

### 2.3 std.df — LOW direct conflicts (no DataFrame exists)

No existing DataFrame/Series type found anywhere in `src/lib/`. `std.df` is greenfield.

**Near-conflicts:**
1. `csv` — `common/csv/` already handles CSV I/O; `std.df` should compose this, not reimplement.
2. `statistics` — `common/statistics/` has `descriptive.spl`, `correlation.spl`; `df.describe()` / `df.corr()` should delegate.
3. `sum`, `min`, `max`, `mean` — free functions in `std.df` (column aggregates) would shadow `math.spl` shorthand aliases at the same import scope.
4. `transform` — `common/csv/transform.spl` has that name; `std.df` transform ops would need a distinct export name.
5. `Series` — not taken anywhere in `src/lib/`.

**Method-only rule applies here too:** `sum`, `min`, `max`, `mean` in `std.df` must be methods on `DataFrame`/`Series`, not free functions. Free functions for scalars belong to `std.math` only.

**Recommendation:** `std.df` is cleanest of the four namespaces. Compose `std.common.csv` for file I/O and `std.common.statistics` for aggregates. Qualify column aggregates as methods on `DataFrame`/`Series`.

### 2.4 std.ml — MODERATE conflicts (ML already scattered)

`nogc_async_mut/ml/` already exists and partially overlaps. `common/pure/nn/` has loss, norm, pooling. `nogc_sync_mut/torch/` is a PyTorch FFI bridge.

**Conflicts:**
1. `fit` — not a top-level name in `src/lib/` currently, but `nogc_async_mut/ml/async_training.spl` likely defines training loops that would conflict with an sklearn-style `model.fit()` protocol.
2. `score` — not found at top level; safe to introduce.
3. `loss` — `common/pure/nn/loss.spl` already exports a `loss` module; `std.ml.loss` would shadow.
4. `norm` — `common/pure/nn/norm.spl` has BatchNorm, LayerNorm; `std.ml.norm` would collide.
5. `data_pipeline` — already in `nogc_async_mut/ml/data_pipeline.spl`; `std.ml` DataLoader must reuse not duplicate.
6. `Device` — already defined in `tensor.spl` for cpu/cuda routing; `std.ml` must reuse same type.

**Recommendation:** `std.ml` should be the canonical facade; `nogc_async_mut/ml/` and `common/pure/nn/` become implementation layers re-exported through it. Rename `nn/norm.spl` exports to `LayerNorm`, `BatchNorm` (already descriptive enough to avoid collision with scalar `norm`).

---

## 3. Reuse Recommendations

| New namespace | Reuse (do not duplicate) |
|---------------|-------------------------|
| `std.linalg` | Compose `std.common.linear_algebra` types as internal impls; re-export `decomposition`, `eigenvalues`, `solve` through the new facade. Reuse `std.math` for scalar fallbacks. |
| `std.ndarray` | Wrap or rename existing `Tensor<T, N>` from `nogc_sync_mut/src/tensor.spl`. Reuse `DType`, `Device`. Reuse `std.math` for elementwise scalar ops. |
| `std.df` | Compose `std.common.csv` for CSV I/O. Compose `std.common.statistics.descriptive` for `describe()`/`corr()`. Use `std.common.encoding` for string column UTF-8 handling. Use `std.io` (via `nogc_sync_mut` io layer) for file read/write. |
| `std.ml` | Facade over `nogc_async_mut/ml/` (async training), `common/pure/nn/` (loss/norm/pooling), `nogc_sync_mut/torch/` (PyTorch FFI). Reuse `std.ndarray.NDArray` / `Tensor` as the tensor type. Reuse `std.common.statistics` for metrics. |

**Units:** `common/engine/units.spl` is game-engine-oriented. Do not reuse for unit-aware arrays — dimensional analysis for scilib (e.g., Quantity<T, Unit>) would need new types in `std.linalg` or a separate `std.units` module. The existing file should not be renamed.

---

## 4. Physical Layout Proposal

### Guiding principle

Tier is determined by the lowest-common-denominator of what the module needs:

| Requirement | Tier |
|-------------|------|
| Pure math, no I/O, no allocation side-effects | `common/` |
| Synchronous I/O, FFI, mutable state, no GC | `nogc_sync_mut/` |
| Async training loops, GC-backed model graphs | `gc_async_mut/` |

Existing `common/linear_algebra/` lives in `common/` — it is pure-function math. `std.linalg` must stay at `common/` tier for the same reason. `tensor.spl` was placed in `nogc_sync_mut/` because its PyTorch FFI requires mutable handles; `std.ndarray` with a CUDA-Fortran backend will similarly need `nogc_sync_mut/` for FFI calls (unless Option A above moves storage behind a trait, in which case the trait definition goes in `common/` and the FFI impl goes in `nogc_sync_mut/`).

### Proposed layout

```
src/lib/
  common/
    linalg/          # std.linalg — pure math surface (rename of common/linear_algebra/)
      types.spl      # Matrix<T>, Vector<T>, Scalar<T> wrappers; re-exports from decomp/eigen
      blas_pure.spl  # Pure-Simple reference BLAS (axpy, dot, nrm2, gemv)
      lapack_pure.spl# Pure-Simple reference LAPACK (gesv, potrf, gesvd)
      decomp.spl     # LU, QR, Cholesky (absorbs existing decomposition.spl)
      eigen.spl      # eigenvalues (absorbs existing eigenvalues.spl)
      solve.spl      # linear system solving (absorbs existing solve.spl)
      mod.spl

  nogc_sync_mut/
    ndarray/         # std.ndarray — NDArray surface (FFI to CUDA-Fortran or libtorch)
      types.spl      # NDArray<T,N>, DType (re-export), Device (re-export), Shape, Index
      factory.spl    # zeros, ones, linspace, arange, eye, from_slice
      ops.spl        # elementwise, broadcasting (methods only — no free fn sum/mean/etc.)
      index.spl      # slicing, fancy indexing
      io.spl         # load_npy, save_npy (delegates to nogc_sync_mut io layer)
      backend.spl    # StorageBackend trait + dispatch (CUDA-Fortran / libtorch impls)
      mod.spl
    df/              # std.df — DataFrame surface (synchronous I/O, no GC needed)
      types.spl      # DataFrame, Series<T>, Index, Column
      construct.spl  # from_csv, from_dict, from_ndarray
      ops.spl        # select, filter, groupby, join, pivot (methods on DataFrame)
      agg.spl        # .sum()/.mean()/.min()/.max()/.describe() — methods, not free fns
      io.spl         # read_csv (compose common/csv), write_csv, read_parquet (new)
      mod.spl

  gc_async_mut/
    ml/              # std.ml — sklearn-style ML surface (GC for model state, async training)
      types.spl      # Estimator trait, Transformer trait, Pipeline
      linear.spl     # LinearRegression, Ridge, Lasso
      ensemble.spl   # RandomForest, GradientBoosting
      nn/            # Neural net facade (over common/pure/nn/)
        layers.spl
        optimizers.spl
        loss.spl     # re-exports common/pure/nn/loss — does not redefine
      metrics.spl    # accuracy, f1, roc_auc (delegates to common/statistics)
      data.spl       # train_test_split, DataLoader (re-exports nogc_async_mut/ml/data_pipeline)
      mod.spl
```

**Rationale for split:**
- `std.linalg` stays in `common/` — pure math matching the tier of the existing `linear_algebra/` implementation it absorbs.
- `std.ndarray` and `std.df` go in `nogc_sync_mut/` — they need FFI or file I/O but not GC, matching the tier where `tensor.spl` already lives.
- `std.ml` goes in `gc_async_mut/` because training loops are async, model graphs require dynamic GC allocation, and the existing `nogc_async_mut/ml/` already points that direction.

---

## 5. Typed-Wrapper Gaps

The project constraint is "no primitive types in public surface." Current state:

| Required type | Status | Action needed |
|---------------|--------|---------------|
| `Float64` | Not a public wrapper class; appears only as a JS `TypedArrayKind` enum variant and a baremetal string intern enum. | **Add:** `struct Float64` wrapping `f64` in `std.ndarray.types` or a shared `std.scilib_types` module. |
| `Float32` | Same situation as Float64. | **Add** in same location. |
| `Index` | `type Index = i64` exists in `nogc_sync_mut/failsafe/panic.spl` (internal). Not a public scilib type. | **Add** as public `struct Index` wrapping `i64` in `std.ndarray.types`. |
| `Shape` | Not defined anywhere in `src/lib/`. | **Add** as `struct Shape` (wraps `[Index]`) in `std.ndarray.types`. |
| `DType` | Already a proper enum in `nogc_sync_mut/src/tensor.spl`. | **Re-export** from `std.ndarray`; do not redefine. |
| `Device` | Already a struct in `tensor.spl` (cpu/cuda). | **Re-export** from `std.ndarray`. |
| `Scalar<T>` | Not defined. | **Add** in `std.linalg.types` as a zero-rank wrapper. |
| `Matrix<T>` | Not a public named type (only `Tensor<T,2>` which is alias-blocked by parser). | **Add** as `struct Matrix<T>` in `std.linalg.types` (wraps `NDArray<T,2>`). |
| `Vector<T>` | Same — `Tensor<T,1>` aliases are disabled. | **Add** as `struct Vector<T>` in `std.linalg.types`. |
| `Series<T>` | Not defined. | **Add** in `std.df.types`. |
| `DataFrame` | Not defined. | **Add** in `std.df.types`. |

**Compiler blocker noted:** Generic type aliases with integer params (`Tensor<T, 2>`) are currently unsupported by the parser (comment in `tensor.spl` line 645, 650). `Matrix<T>` and `Vector<T>` must be concrete struct wrappers, not aliases, until the parser is fixed. This should be filed as a feature request in `compiler_requests.md`.

---

## Summary

**Top 5 conflicts:**
1. `common/linear_algebra/` — entire module collides with `std.linalg`; rename to `common/linalg/` and make it the internal implementation absorbed by `std.linalg`.
2. `Tensor<T,N>` in `nogc_sync_mut/src/tensor.spl` — covers ~90% of `std.ndarray.NDArray`; storage backend differs (libtorch vs CUDA-Fortran); arch must pick rename+pluggable-backend (Option A) or two coexisting types (Option B). Do not silently duplicate.
3. `sum`/`mean`/`min`/`max`/`norm` — exist as `math.spl` free functions and `Tensor` methods; rule: these must be **methods on array/df types only**; `std.math` owns the free-function scalar surface.
4. `common/pure/nn/loss.spl` and `nn/norm.spl` — module names collide with `std.ml.loss` and `std.ml.norm`; `std.ml` re-exports them, not redefines.
5. `DType` and `Device` in `tensor.spl` — must be re-exported by `std.ndarray`, not redefined.

**Physical layout:** `std.linalg` → `src/lib/common/linalg/`; `std.ndarray` + `std.df` → `src/lib/nogc_sync_mut/{ndarray,df}/`; `std.ml` → `src/lib/gc_async_mut/ml/`.
