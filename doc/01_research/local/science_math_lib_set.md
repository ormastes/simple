<!-- codex-research -->
# Science Math Lib Set Local Research

**Date:** 2026-05-05
**Scope:** async and nogc science/math library consistency across `std.ndarray`, `std.linalg`, `std.df`, math blocks, Fortran-compatible BLAS/LAPACK shims, and future SIMD/CUDA/PyTorch backends.

## Current Implementation Map

- `src/lib/nogc_async_mut/ndarray/mod.spl` implements the active `NDArray` surface: typed scalar wrappers (`Float64`, `Int64`, `Bool`), `DType`, constructors (`array`, `array_i64`, `array_bool`, `zeros`, `ones`, `full`, `empty`, `eye`, `arange`, `linspace`), shape/stride metadata, indexing, slicing, gather/mask, reshape/transpose/squeeze, and broadcasted elementwise operations.
- `src/lib/nogc_sync_mut/ndarray/mod.spl` is a thin facade over `std.nogc_async_mut.ndarray.*`, so the sync and async nogc ndarray APIs are currently consistent by construction.
- `src/lib/common/linalg/ndarray_core.spl` owns shared `Device`, `Layout`, `KernelProfile`, `Index`, `Axis`, `Shape`, `Stride`, `SliceSpec`, `BroadcastPlan`, and shape/stride/broadcast helpers.
- `src/lib/nogc_async_mut/linalg/mod.spl` implements the active linalg surface: `vector_from`, `matrix_from_rows`, `zeros_matrix`, `full_matrix`, `eye_matrix`, `dot`, `axpy`, `gemv`, `gemm`, `norm`, and `solve`.
- `src/lib/common/linalg/mod.spl` and `src/lib/nogc_sync_mut/linalg/mod.spl` are re-export facades over `std.nogc_async_mut.linalg.*`.
- `src/lib/nogc_sync_mut/df/mod.spl` implements the active Pandas-like seed: `Symbol`, `DfValue`, `Series`, `SeriesErased`, `DataFrame`, column construction, row construction, column lookup, assign/drop/rename, dtype listing, and astype.
- `src/runtime/scilib/{cublas_shim.c,cusolver_shim.c,mock_shim.c}` exists as the planned runtime shim location. The current passing scilib tests exercise Simple fallback/mock behavior, not complete real BLAS/LAPACK coverage.
- Older mature scalar/list APIs remain in `src/lib/common/math.spl`, `src/lib/common/statistics/`, `src/lib/common/numerical_methods/`, and `src/lib/common/linear_algebra/`. These are useful kernels but do not yet share one public science namespace with the newer `NDArray` layer.
- Math block support exists in both compiler surfaces: `src/compiler/15.blocks/blocks/builtin_blocks_math.spl` for self-hosted block definitions and `src/compiler_rust/compiler/src/blocks/math/` for the Rust compiler runtime math evaluator.

## Existing Tests And Artifacts

- Focused scilib specs exist under `test/feature/scilib/`: ndarray constructors, broadcasting, slicing, indexing, BLAS axpy/gemm, LAPACK solve, DataFrame construction/column ops, and math block matmul/slice/inv/solve.
- `SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib --mode=interpreter` passed on 2026-05-05 with `Failed: 0`.
- Prior research exists under `doc/01_research/scilib_fortran_port/`, especially Python API surface, math block lowering, ABI risk, and naming harmony.
- Prior design exists at `doc/05_design/scilib_port_architecture.md`. It covers `std.ndarray`, `std.linalg`, `std.df`, `std.ml`, CUDA/OpenBLAS/mock backends, and a libtorch backend concept, but it predates the current implementation state and is not a canonical full-suite roadmap.

## Gap Analysis

- **Async/nogc consistency:** `ndarray` and `linalg` are consistent across `nogc_async_mut` and `nogc_sync_mut` through re-export facades. `df` currently exists only in `nogc_sync_mut`, so async/nogc DataFrame consistency is incomplete.
- **NumPy parity:** v1 covers constructors, basic shape/stride metadata, slicing/indexing, broadcasting, and a small elementwise/linalg set. Missing broad parity includes reductions by axis, dtype conversions beyond F64/I64/Bool, random, I/O, sorting, concat/stack, FFT, sparse arrays, masked arrays, and many ufuncs.
- **SciPy parity:** existing older `common/numerical_methods` and `common/statistics` provide kernels, but there is no unified `std.scipy`-style package surface for optimize, integrate, special, stats, signal, sparse, or spatial.
- **Pandas parity:** `DataFrame` and `Series` seed APIs exist, but groupby, joins, concat, missing-value semantics, indexing modes, CSV/parquet I/O, datetime, rolling/window ops, and categorical data are not implemented.
- **Fortran library support:** the intended model is C ABI shims over BLAS/LAPACK/cuBLAS/cuSOLVER/OpenBLAS, not direct Fortran compiler integration. LAPACK/BLAS task docs define the desired symbols, but complete wrapper/shim/API coverage is not present.
- **Math block support:** v1 runtime string-interpreter support is the right incremental path. Full type-directed HIR lowering, static dispatch, and optimization remain future compiler work.
- **Backend acceleration:** current implementation can model `Device`/`KernelProfile`, but SIMD, CUDA, and PyTorch/libtorch backend selection are not yet expressed as a single storage/backend contract in the implemented `NDArray`.

## Recommended Roadmap

1. Stabilize one canonical typed `NDArray` contract and make `nogc_async_mut`, `nogc_sync_mut`, and future `gc_async_mut` facades consume it.
2. Fill NumPy-core before wider SciPy/Pandas: axis reductions, ufunc registry, dtype conversion, concatenate/stack, sort/argsort, random seedable basics, and `.npy`/text I/O.
3. Promote `std.linalg` from fallback Simple loops to a backend-dispatched surface with mock, CPU scalar, CPU SIMD, OpenBLAS/LAPACKE, CUDA/cuBLAS/cuSOLVER, and PyTorch/libtorch adapters.
4. Extend `std.df` after ndarray core is stable: typed `Series<T>`, missing values, groupby narrow path, joins/concat, CSV I/O, and async facade parity.
5. Unify older `common/statistics`, `common/numerical_methods`, and `common/linear_algebra` as SciPy-style modules that consume `NDArray` when shape-aware behavior is needed and keep list/scalar overloads as compatibility wrappers.
6. Keep math blocks out of DataFrame operations. Use math blocks for ndarray/linalg expressions only, with runtime interpretation in v1 and HIR lowering as a later compiler project.

