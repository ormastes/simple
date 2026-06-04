# Core GEMM Dispatcher

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** High-performance GEMM with multiple implementation strategies

## Simple Approach

This exercise implements a GEMM dispatcher that routes matrix multiplication to the
optimal implementation based on matrix dimensions and available hardware:
- **Shared memory tiled GEMM:** For general matrices
- **Tensor core GEMM:** For aligned dimensions on tensor-core capable hardware
- **SIMD CPU fallback:** For small matrices where GPU overhead dominates

The dispatcher inspects matrix dimensions at runtime and selects the best kernel.

## Concepts Covered

- GEMM dispatch strategy based on matrix size
- Shared memory tiled implementation
- Tensor core implementation for aligned dimensions
- CPU SIMD fallback for small matrices
- Performance heuristics for kernel selection

## Files

- `main.spl` - GEMM dispatcher with multiple backends
- `spec.spl` - Tests for each GEMM backend
