# Matrix Multiply: SIMD vs GPU

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** GPU matrix multiply optimization

## Simple Approach

This exercise compares two approaches to matrix multiplication in Simple:
1. **SIMD (CPU):** Using `@simd` with `Vec4f`/`Vec8f` vectorized types
2. **GPU kernel:** Using `@gpu_kernel` with shared memory tiling

Simple provides both `std.simd` and `std.gpu` modules, allowing direct comparison
of the same algorithm on different hardware.

Key features:
- **SIMD types:** `Vec4f`, `Vec8f` for 128-bit and 256-bit vectorized floats
- **GPU shared memory:** `@shared` annotation for tile-based matmul
- **Unified interface:** Both implementations share the same function signature
- **Benchmarking:** Built-in timing to compare throughput

## Concepts Covered

- SIMD vectorized matrix multiplication with `Vec4f`/`Vec8f`
- GPU tiled matrix multiplication with shared memory
- Performance comparison between CPU SIMD and GPU
- Choosing the right compute target based on matrix size

## Files

- `main.spl` - SIMD and GPU matmul implementations with benchmarks
- `spec.spl` - Tests verifying both produce correct results
