# Parallel Iterators (Thrust Equivalent)

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Thrust library for parallel algorithms (transform, reduce, scan)

## Simple Approach

Simple replaces Thrust's C++ template-based parallel iterators with first-class
functional patterns that dispatch to GPU kernels. Operations like `map`, `reduce`,
and `scan` are expressed using lambdas and placeholder syntax (`_ * 2`), with the
GPU backend handling parallelization transparently.

Key differences from Thrust:
- **No iterator pairs:** Use array/slice directly, not `begin()`/`end()`
- **Lambda syntax:** `\x: x * 2` or `_ * 2` instead of C++ functors
- **Pipeline operator:** `data |> gpu_map(_ * 2) |> gpu_reduce(0.0, _ + _)`
- **Automatic backend:** GPU dispatch is implicit, no `thrust::device` policy

## Concepts Covered

- `gpu_map` - parallel transform
- `gpu_reduce` - parallel reduction
- `gpu_scan` - prefix sum (inclusive/exclusive)
- `gpu_filter` - parallel compaction
- `gpu_sort` - parallel sort
- Pipeline composition with `|>`

## Files

- `main.spl` - Parallel iterator operations with GPU backing
- `spec.spl` - Tests for parallel operations
