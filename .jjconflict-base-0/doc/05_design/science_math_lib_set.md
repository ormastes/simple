<!-- codex-design -->
# Science Math Lib Set Detail Design

**Date:** 2026-05-05
**Status:** Scalar science-lib slice plus narrow SIMD/OpenBLAS/CUDA/PyTorch probes implemented. OpenBLAS dot/GEMV/GEMM/solve and CUDA/PyTorch dot/GEMV/GEMM/solve/inv can be selected by configuration with scalar fallback where available. SIMD has focused availability, spec wall-clock, and public operation latency gates, including contiguous 1-D Float64 NDArray add/sub/mul/div, scalar add/sub/mul/div, whole-array sum/mean, Float32 `sum_f32`/`mean_f32`, Float32 scalar add/sub/mul/div with scalar tail handling, and Float64/Float32 abs/square/neg unary probes. CUDA also has explicit cuSOLVER-backed `cuda_solve` for Float64 vector right-hand sides and `cuda_inv` through multiple right-hand sides. CUDA now has explicit array-shaped device storage, copy-producing reshape/flatten/2-D transpose shape operations, explicit 1-D concatenate/stack combine operations, device-side Float64 array-array and array-scalar add/sub/mul/div kernels, scalar-result sum/mean/min/max reduction kernels, 2-D sum/mean-axis kernels, device-side 1-D/2-D slicing including positive steps, negative bounds, negative steps, and empty slices. PyTorch has copied Float64 tensor ownership for host round-trips plus interpreter-verified resident 1-D through 4-D zeros/ones/full/empty/random-uniform/random-normal creation, arange/linspace/eye creation, add/sub/mul/div/atan2, 2-D matmul, resident solve/inverse, scalar add/sub/mul/div/pow, abs/neg/square/sqrt/exp/log/relu/leaky_relu/gelu/sigmoid/tanh/sin/cos/tan/asin/acos, softmax/log_softmax, scalar reductions/statistics/determinant operations, 2-D sum/mean/min/max/argmin/argmax-axis reductions, clone/unsqueeze/squeeze/1-D through 4-D reshape/flatten/2-D transpose/rank-2 through rank-4 permute/contiguous materialization, positive-bound 1-D/2-D slicing, and 1-D concatenate/stack. Broad SIMD, broad CUDA-native NDArray kernels, broad cuSOLVER coverage, and PyTorch zero-copy/DLPack verification remain future work.
**Future Backend Plan:** `doc/03_plan/science_math_backend_extension_research_plan.md`, `doc/05_design/science_math_backend_extensions.md`.

## Deliverable Shape

The science/math library set should be delivered in staged slices:

1. **Core consistency:** make `std.ndarray`, `std.linalg`, and `std.df` available consistently across `nogc_async_mut` and `nogc_sync_mut`; define intended `gc_async_mut` wrappers.
2. **NumPy core:** constructors, dtype/device/layout, indexing/slicing, broadcasting, ufuncs, axis reductions, concat/stack, sorting, random basics, and array I/O.
3. **Fortran-compatible linalg:** BLAS/LAPACK Layer A/B/C wrappers with mock/OpenBLAS/CUDA backends.
4. **SciPy-style modules:** stats, optimize, integrate, special, signal, sparse, and spatial as modules over ndarray plus scalar/list compatibility wrappers.
5. **Pandas-style DataFrame:** labeled `Series`/`DataFrame`, missing values, groupby, joins/concat, reshape, CSV/text I/O, datetime/categorical follow-up.
6. **Backend acceleration:** SIMD first for CPU hot loops, CUDA for BLAS/LAPACK/device arrays, PyTorch/libtorch as optional tensor backend.

## Public Types

- `Float64`, `Float32`, `Int64`, `Bool`: typed scalar wrappers.
- `Index`, `Axis`, `Shape`, `Stride`: dimensional metadata.
- `DType`, `Device`, `Layout`, `KernelProfile`: dispatch metadata.
- `NDArray`: dynamic-rank typed array with data, shape, strides, offset, dtype, device, layout, and backend profile.
- `Matrix<T>`, `Vector<T>`: rank-constrained wrappers over `NDArray`.
- `Series`, `DataFrame`: labeled data containers over typed arrays.
- `LinalgError`, `NdarrayError`, `DfError`, `BackendError`: error enums returned through `Result`.

## Backend Contract

Each backend adapter must declare capabilities:

- supported dtypes,
- supported layouts,
- supported devices,
- in-place versus out-of-place behavior,
- allocation behavior,
- blocking behavior,
- and required runtime symbols.

The scalar backend is always available. Optional backends may fail cleanly with `UnsupportedDType`, `UnsupportedLayout`, `BackendUnavailable`, or `BlockingOperationInAsyncContext` when required.

## SIMD Plan

- Add `CpuSimdBackend` behind the same ndarray/linalg operations.
- Start with contiguous F64 elementwise add/mul, simple unary ops, reductions, dot, axpy, and small matrix kernels.
- Dispatch only when shape is contiguous, dtype is supported, and input length exceeds a minimum threshold.
- Verify scalar parity with deterministic fixtures and record latency deltas.

## CUDA Plan

- Complete shim symbols in `src/runtime/scilib/` for CUDA memory, BLAS, and LAPACK.
- Keep host/device movement explicit through `Device` and backend-owned buffers.
- Use row-major host staging plus explicit row-major to column-major conversion for cuSOLVER paths such as `cuda_solve` and `cuda_inv`.
- Use `SIMPLE_BLAS_BACKEND=mock` for normal specs; add GPU-only tests for real CUDA.
- Ensure async APIs do not hide blocking host/device sync without an explicit scheduling wrapper.

## PyTorch Backend Plan

- Add `LibtorchBackend` as an optional adapter over the existing tensor/libtorch infrastructure.
- Use it for broad tensor kernels and compatibility when available.
- Do not make libtorch required for core correctness.
- Keep autograd and neural network APIs in `std.ml` or a separate tensor/autograd layer.

## Math Block Plan

- v1 math blocks call public ndarray/linalg APIs through the runtime interpreter.
- Supported v1 expressions: `A @ B`, broadcast add/mul, `A[i:j,k]`, `.T`, `reshape`, `sum(axis)`, `mean(axis)`, `inv(A)`, and `solve(A,b)`.
- DataFrame expressions are excluded from math blocks.
- v2 HIR-lift is a compiler project and should only start after library semantics are stable.

## Test Plan

- Extend `test/feature/scilib/` with one spec per public API cluster.
- Keep using built-in matchers only.
- Required focused commands:
  - `SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib --mode=interpreter`
  - targeted specs for any changed namespace
  - backend parity tests when SIMD/CUDA/PyTorch adapters are implemented
- Every new requirement must map to a real assertion and at least one error-path test.

## Implementation Order

1. Document final requirement selections and NFRs.
2. Normalize namespace exports and add missing async/nogc DataFrame facade.
3. Complete NumPy-core ndarray methods before expanding SciPy/Pandas.
4. Complete linalg Layer A/B/C wrappers and mock backend parity.
5. Add SIMD backend.
6. Add CUDA backend.
7. Add optional PyTorch/libtorch backend.
8. Add broader SciPy/Pandas modules after ndarray/linalg contracts are stable.
