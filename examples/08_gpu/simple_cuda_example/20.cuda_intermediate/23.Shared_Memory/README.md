# Exercise 23: Shared Memory Reduction Patterns

## Parallel Reduction

Reduction is a fundamental GPU pattern: combining N values into a single
result (sum, min, max, etc.). Shared memory makes this fast by keeping
intermediate values in low-latency block-local memory.

### The Reduction Tree

For a sum reduction of 8 elements in one block:

```
Step 0:  [a0] [a1] [a2] [a3] [a4] [a5] [a6] [a7]
Step 1:  [a0+a4] [a1+a5] [a2+a6] [a3+a7]  --   --   --   --
Step 2:  [s0+s2]  [s1+s3]   --      --     --   --   --   --
Step 3:  [final]    --       --      --     --   --   --   --
```

Each step halves the active threads. After log2(N) steps, thread 0
has the block's result.

### Three Variants

1. **Naive interleaved:** Thread `i` adds element at `i + stride`.
   Simple but causes bank conflicts due to interleaved addressing.

2. **Sequential addressing:** Thread `i` adds element at `i + stride`,
   but accesses are sequential, avoiding bank conflicts.

3. **First-add during load + unroll last warp:** Two optimizations:
   - Each thread loads and adds two elements during the initial load,
     halving the number of reduction steps.
   - The last 32 threads (one warp) execute in lockstep, so
     `gpu_syncthreads()` calls can be skipped (warp-synchronous).

### Performance Comparison

| Variant | Bank Conflicts | Sync Overhead | Load Efficiency |
|---------|---------------|---------------|-----------------|
| Naive interleaved | Yes | Full | 1x load |
| Sequential addressing | No | Full | 1x load |
| First-add + unroll | No | Reduced | 2x load (halves steps) |

## Files

- `main.spl` - Three reduction variants with increasing optimization
- `spec.spl` - Tests verifying all variants produce correct sums

## Learning Goals

- Implement parallel reduction with shared memory
- Understand bank conflicts and sequential addressing
- Apply the "first add during load" optimization
- Understand warp-synchronous execution for the final warp
