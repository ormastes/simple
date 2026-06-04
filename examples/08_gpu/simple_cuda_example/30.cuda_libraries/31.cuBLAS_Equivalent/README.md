# GPU BLAS Operations

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** cuBLAS library for linear algebra on GPU

## Simple Approach

Instead of wrapping cuBLAS, Simple provides GPU-accelerated linear algebra through
native kernels and the `std.gpu` module. Matrix operations are expressed as kernel
launches with familiar mathematical notation.

Key differences from cuBLAS:
- **No opaque handles:** No `cublasCreate()`/`cublasDestroy()` lifecycle
- **Direct kernel launch:** Write or use built-in GEMM kernels directly
- **Dimension checking:** Compile-time dimension validation with `Tensor<rows, cols>`
- **Error handling:** `Result<T, GpuError>` instead of `cublasStatus_t`

## Concepts Covered

- GPU matrix multiplication (GEMM)
- GPU vector dot product
- GPU vector scaling (AXPY)
- Shared memory tiling for performance
- Dimension-checked tensor operations

## Files

- `main.spl` - BLAS operations: GEMM, dot product, AXPY
- `spec.spl` - Tests for correctness of GPU linear algebra
