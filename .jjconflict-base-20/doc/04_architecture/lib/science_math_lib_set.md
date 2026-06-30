<!-- codex-design -->
# Science Math Lib Set Architecture

**Date:** 2026-05-05
**Status:** Design roadmap; no implementation changes in this document.
**Related:** `doc/05_design/scilib_port_architecture.md`, `doc/03_plan/agent_tasks/scilib_port_ndarray.md`, `doc/03_plan/agent_tasks/scilib_port_blas.md`, `doc/03_plan/agent_tasks/scilib_port_lapack.md`, `doc/03_plan/agent_tasks/scilib_port_math_block.md`, `doc/03_plan/science_math_backend_extension_research_plan.md`, `doc/05_design/science_math_backend_extensions.md`.

## Architecture Goal

Provide one consistent science/math library family across async and nogc stdlib variants while preserving a small portable correctness baseline and allowing later SIMD, CUDA, OpenBLAS/LAPACKE, and PyTorch/libtorch acceleration.

## Namespace Layers

| Layer | Namespace | Role |
| --- | --- | --- |
| Typed array core | `std.ndarray` | `NDArray`, `Shape`, `Stride`, `Index`, dtype/device/layout, constructors, indexing, slicing, broadcasting, ufuncs, reductions |
| Dense linalg | `std.linalg` | BLAS/LAPACK-like operations over `NDArray`: dot, axpy, gemv, gemm, solve, inv, decompositions |
| Statistics/numerics | `std.stats`, `std.scipy.*` | Statistics, optimize, integrate, special, signal, sparse, spatial; consumes ndarray where shape-aware |
| Data analysis | `std.df` | `Series`, `DataFrame`, labeled columns, groupby, joins, missing values, file I/O |
| ML/tensor | `std.ml` / tensor backend | Estimators, preprocessing, metrics, optional PyTorch/libtorch acceleration |
| Expression sugar | `math{}` / `m{}` | ndarray/linalg expression syntax only; no DataFrame semantics |

## Backend Capsule

The science stack is a virtual capsule with a public API shell and backend adapters:

- `ScalarCpuBackend`: portable baseline and interpreter fallback.
- `CpuSimdBackend`: future contiguous-buffer acceleration.
- `OpenBlasBackend`: host BLAS/LAPACK through C ABI shims.
- `CudaBackend`: cuBLAS/cuSOLVER plus CUDA memory through runtime shims.
- `LibtorchBackend`: optional PyTorch/libtorch tensor kernel adapter.
- `MockBackend`: deterministic CI/test backend.

Public APIs depend on a backend capability contract, not on concrete C/PyTorch/CUDA symbols. Backend selection happens below Layer C public APIs and returns `Result` errors for unsupported dtype/layout/device combinations.

## Async And Nogc Family Rule

- `common` owns pure algorithms and shared typed metadata.
- `nogc_async_mut` owns allocation-aware ndarray/linalg implementations and backend handles.
- `nogc_sync_mut` re-exports the async-compatible surface where no scheduling distinction exists.
- `gc_async_mut` may expose convenience wrappers and higher-level ML/data APIs, but it must not become the only implementation of core ndarray/linalg behavior.
- Any operation that allocates must be either a constructor/conversion/workspace builder or documented as allocating. Hot elementwise/linalg paths must prefer caller-owned output buffers in future phases.

## Math Block Boundary

`math{}` integrates only with ndarray/linalg:

- v1: runtime string interpreter for `@`, slices, transpose/method normalization, `inv`, `solve`, `sum`, and `mean`.
- v2: optional HIR-lift and type-directed lowering when compiler work is explicitly scheduled.
- DataFrame operations stay in method calls (`df.col`, `groupby`, `join`) and never enter math blocks.

## Fortran-Compatible Library Rule

Fortran support means compatible library routines, not direct Fortran source support:

- Layer A raw externs use stable `rt_blas_*`, `rt_lapack_*`, and `rt_cuda_*` symbols.
- Layer B unwraps typed wrappers, handles row-major to column-major conversion, workspace allocation, pivot conversion, and backend handles.
- Layer C public APIs expose typed Simple wrappers only.
- Direct nvfortran or Fortran-mangled symbol binding is out of scope unless a separate compiler/FFI requirement is approved.

## Extension Path

1. **SIMD:** add backend after scalar API stability. Dispatch only for contiguous supported dtypes; fallback to scalar otherwise.
2. **CUDA:** complete C ABI shim symbols, CUDA memory lifecycle, cuBLAS/cuSOLVER wrappers, and GPU-only verification.
3. **PyTorch:** add optional libtorch backend for ndarray/tensor kernels and keep autograd separate.

## Verification Gates

- Focused scilib interpreter specs must remain green under `SIMPLE_BLAS_BACKEND=mock`.
- Each public API requirement must have a feature spec with real assertions and error-path coverage.
- Backend parity tests compare scalar, mock, SIMD, CUDA, and PyTorch results on small deterministic fixtures where those backends are enabled.
- Performance-sensitive backend dispatch must record warm startup, representative operation latency, and max RSS before release.
