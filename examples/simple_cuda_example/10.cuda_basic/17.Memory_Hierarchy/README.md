# Exercise 17: Memory Hierarchy

## CUDA Memory Model vs Simple GPU API

CUDA exposes a multi-level memory hierarchy. Simple wraps these with safe,
typed APIs that prevent common errors like uninitialized shared memory or
out-of-bounds global accesses.

### Memory Levels

| Level | CUDA | Simple | Scope | Latency |
|-------|------|--------|-------|---------|
| **Registers** | `int x = 0;` | `val x = 0` | Per-thread | ~1 cycle |
| **Shared** | `__shared__ float s[N];` | `gpu_shared_mem<f32>(N)` | Per-block | ~5 cycles |
| **Global** | `float* d; cudaMalloc(&d, N);` | `gpu_alloc<f32>(N)` | All threads | ~400-600 cycles |
| **Constant** | `__constant__ float c[N];` | `@gpu_constant val c = ...` | All threads (cached) | ~5 cycles (cached) |

### Key Differences from CUDA C

1. **Shared memory is typed and sized at call site:**
   CUDA uses `__shared__` declarations; Simple uses `gpu_shared_mem<T>(size)`.

2. **No raw pointers:** All GPU memory is managed through `GpuBuffer<T>`, which
   tracks size and ensures safe access.

3. **Explicit sync:** `gpu_syncthreads()` is required before reading shared memory
   written by other threads, same as `__syncthreads()` in CUDA.

4. **Result-based errors:** Memory allocation returns `Result<GpuBuffer<T>, GpuError>`
   instead of error codes.

### Tiling Pattern for Shared Memory

The core optimization pattern:

```
For each tile of the output:
  1. Load tile from global -> shared memory
  2. gpu_syncthreads()
  3. Compute on shared memory (fast)
  4. gpu_syncthreads()
  5. Write result back to global
```

This reduces global memory accesses from O(N) to O(N / TILE_SIZE) per thread.

## Files

- `main.spl` - Matrix multiplication: naive vs shared-memory tiled
- `spec.spl` - Correctness tests comparing both variants

## Learning Goals

- Understand the GPU memory hierarchy
- Use `gpu_shared_mem<f32>()` for block-local fast memory
- Apply the tiling pattern to reduce global memory traffic
- Use `gpu_syncthreads()` correctly to avoid race conditions
