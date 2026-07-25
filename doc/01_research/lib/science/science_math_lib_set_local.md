<!-- codex-research -->
# Science Math Lib Set Domain Research

**Date:** 2026-05-05
**Scope:** external architecture model for a complete science/math library set inspired by NumPy, SciPy, pandas, BLAS/LAPACK/Fortran ecosystems, SIMD, CUDA, and PyTorch.

## Reference API Families

- **NumPy-style core:** n-dimensional typed arrays, shape/stride metadata, broadcasting, ufuncs, reductions, indexing/slicing, dtype conversion, random, FFT, linear algebra, I/O, and memory layout controls.
- **SciPy-style domains:** linalg, sparse, optimize, integrate, interpolate, signal, stats, special functions, spatial, and I/O helpers. SciPy generally layers domain algorithms on top of NumPy arrays and delegates heavy dense linear algebra to BLAS/LAPACK.
- **pandas-style data:** labeled `Series` and `DataFrame`, columnar storage, missing values, alignment by labels, indexing modes, groupby, joins, reshape, rolling windows, datetime/categorical/string columns, and file formats.
- **Fortran/BLAS/LAPACK:** practical "Fortran library support" should mean stable ABI-compatible wrappers around BLAS/LAPACK routines through C ABI shims. Direct compiler support for Fortran source or mangled Fortran symbols should not be required for v1.
- **PyTorch/libtorch:** tensor backend and GPU acceleration can be exposed as an `NDArray` storage backend, but autograd and neural-network semantics should remain separate from the scientific ndarray contract unless explicitly requested.

## Backend Lessons

- **CPU scalar backend:** required as the portable correctness baseline and interpreter-friendly fallback.
- **CPU SIMD backend:** should be a backend implementation detail selected by dtype, layout, contiguity, and vector width. Public APIs should not expose SIMD lane types.
- **OpenBLAS/LAPACKE backend:** should serve host BLAS/LAPACK acceleration with the same symbol contract as the CUDA shim where possible.
- **CUDA backend:** should use cuBLAS/cuSOLVER C APIs through stable runtime symbols. CUDA memory ownership must be explicit through `Device.CUDA`, backend handles, and host/device copy boundaries.
- **PyTorch/libtorch backend:** useful for broad tensor kernels and GPU fallback, but should be optional. It must not become the only route to correctness because package size and deployment constraints differ from Simple's core runtime.
- **Mock backend:** essential for interpreter-mode specs. It must compute correct small-N results for tested operations, not return zero-only stubs.

## Design Constraints For Simple

- Public science APIs should use typed wrappers (`Float64`, `Index`, `Shape`, `DType`, `Device`, `NDArray`) rather than raw primitives at module boundaries.
- `Result<T, E>` should be used for invalid shapes, unsupported dtypes, singular matrices, non-convergence, I/O errors, and backend failures.
- `nogc` contexts must avoid hidden allocation in hot operations or clearly move allocation into constructors, workspace builders, and explicit conversion calls.
- Async APIs must not hide blocking native/FFI calls in request paths. Long-running operations need either explicit async scheduling or documented synchronous behavior.
- Math blocks should remain an ergonomic expression layer over ndarray/linalg, not a second DataFrame language and not a hidden way to bypass library error semantics.

## Extension Planning

- **SIMD extension:** add `CpuSimdBackend` after the scalar backend contract is stable. Gate dispatch on contiguous row-major buffers, dtype support, and minimum element counts. Verify with scalar parity tests and representative latency measurements.
- **CUDA extension:** add `CudaBackend` using `rt_cuda_*`, `rt_blas_*`, and `rt_lapack_*` symbols. Keep host/device transfer visible in design and use mock backend tests for CI portability plus GPU-only tests for real devices.
- **PyTorch extension:** add `LibtorchBackend` as an optional backend for tensor kernels. Treat it as a compatibility/acceleration backend, not as the canonical storage model. Keep autograd in `std.ml` or a dedicated tensor/autograd layer.

## Success Definition

A "complete" science/math library set should be defined as staged API compatibility and verified behavior, not a claim of full bit-for-bit NumPy/SciPy/pandas replacement in one change. Completion requires:

- a documented namespace map,
- stable public wrappers,
- a backend contract,
- tests for every required API tier,
- consistent async/nogc facades,
- and clear unsupported/deferred APIs with tracked rationale.

