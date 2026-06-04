# Tensor Core Operations

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** WMMA (Warp Matrix Multiply-Accumulate) API for tensor cores

## Simple Approach

Simple provides tensor core access through high-level matrix fragment operations.
Instead of CUDA's `wmma::fragment` and `wmma::mma_sync`, Simple uses typed tensor
fragments with compile-time dimension checking.

Key differences from CUDA WMMA:
- **Type-safe fragments:** `TensorFragment<16, 16, f16>` instead of `wmma::fragment<wmma::matrix_a, 16, 16, 16, half>`
- **Dimension checking:** Compile-time validation that matrix dimensions are compatible
- **Automatic layout:** No manual row/column major specification needed
- **Accumulator type inference:** `f32` accumulator automatically selected for `f16` inputs

## Concepts Covered

- Tensor fragment loading and storing
- Matrix multiply-accumulate (MMA) on tensor cores
- Mixed-precision computation (f16 inputs, f32 accumulator)
- Tiled GEMM using tensor cores
- ML-oriented matrix operations

## Files

- `main.spl` - Tensor core GEMM with WMMA-style fragments
- `spec.spl` - Tests for tensor core operations
