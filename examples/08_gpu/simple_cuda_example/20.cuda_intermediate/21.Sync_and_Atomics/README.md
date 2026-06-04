# Exercise 21: Synchronization and Atomics

## Thread Synchronization in Simple vs CUDA

When multiple GPU threads access shared data, synchronization is required
to prevent race conditions. Simple provides the same synchronization
primitives as CUDA, with clearer naming.

### Barrier Synchronization

| Simple | CUDA | Scope |
|--------|------|-------|
| `gpu_syncthreads()` | `__syncthreads()` | Block-level barrier |

All threads in a block must reach the barrier before any can proceed.
Use this when threads need to read data written by other threads in
the same block (typically with shared memory).

### Atomic Operations

| Simple | CUDA | Description |
|--------|------|-------------|
| `gpu_atomic_add(ptr, val)` | `atomicAdd` | `*ptr += val`, returns old |
| `gpu_atomic_sub(ptr, val)` | `atomicSub` | `*ptr -= val`, returns old |
| `gpu_atomic_min(ptr, val)` | `atomicMin` | `*ptr = min(*ptr, val)`, returns old |
| `gpu_atomic_max(ptr, val)` | `atomicMax` | `*ptr = max(*ptr, val)`, returns old |
| `gpu_atomic_cas(ptr, cmp, val)` | `atomicCAS` | If `*ptr == cmp`: set `*ptr = val`, returns old |
| `gpu_atomic_exch(ptr, val)` | `atomicExch` | `*ptr = val`, returns old |
| `gpu_atomic_and(ptr, val)` | `atomicAnd` | `*ptr &= val`, returns old |
| `gpu_atomic_or(ptr, val)` | `atomicOr` | `*ptr |= val`, returns old |

### When to Use Atomics

- **Counters:** Multiple threads incrementing a shared counter
- **Reductions:** Finding min/max/sum across all threads
- **Histograms:** Binning elements into shared bins
- **Lock-free data structures:** Compare-and-swap for custom protocols

### Performance Notes

- Atomics are slower than regular memory access (serialized at the hardware level)
- Minimize atomic contention: reduce to block-level first, then atomically combine
- Shared memory atomics are faster than global memory atomics
- `gpu_syncthreads()` is a barrier, not an atomic -- it synchronizes *all* threads in a block

## Files

- `main.spl` - Atomic counters, reductions, histogram, CAS patterns
- `spec.spl` - Correctness tests for each atomic pattern

## Learning Goals

- Use `gpu_syncthreads()` for block-level barriers
- Apply atomic operations for thread-safe updates
- Build a histogram with `gpu_atomic_add`
- Implement min/max reduction with atomics
- Understand compare-and-swap for custom synchronization
