# Exercise 24: Memory Coalescing

## What is Memory Coalescing?

GPU global memory is accessed in large transactions (32, 64, or 128 bytes).
When consecutive threads access consecutive memory addresses, the hardware
can combine (coalesce) their requests into a single transaction. When
threads access scattered addresses, each thread may trigger a separate
transaction, wasting bandwidth.

### Coalesced vs Strided Access

**Coalesced (good):** Thread i reads element i.
```
Thread 0 -> addr[0]
Thread 1 -> addr[1]
Thread 2 -> addr[2]
...
```
One memory transaction serves all 32 threads in a warp.

**Strided (bad):** Thread i reads element i*stride.
```
Thread 0 -> addr[0]
Thread 1 -> addr[stride]
Thread 2 -> addr[2*stride]
...
```
Up to 32 separate memory transactions for one warp.

### Row-Major vs Column-Major

For an MxN matrix stored row-major:
- **Row access (coalesced):** `data[row * N + col]` where `col` varies with thread ID
- **Column access (strided):** `data[row * N + col]` where `row` varies with thread ID

### SIMD Comparison (CPU)

For CPU code, Simple provides `@simd` with `Vec4f`/`Vec8f` for explicit
vectorization. This is the CPU equivalent of coalesced access -- processing
multiple elements per instruction.

| GPU | CPU | Description |
|-----|-----|-------------|
| Coalesced global access | `Vec8f` / `@simd` loop | Process N elements per operation |
| Shared memory | L1 cache / registers | Low-latency local storage |
| Warp (32 threads) | SIMD lane (4-8 floats) | Hardware parallelism unit |

### Performance Impact

Coalesced access can be 10-20x faster than fully strided access.
The difference is most visible with large strides that exceed cache
line boundaries.

## Files

- `main.spl` - Coalesced vs strided GPU access + CPU SIMD comparison
- `spec.spl` - Tests verifying correctness of all variants

## Learning Goals

- Understand memory coalescing and why it matters
- Compare coalesced vs strided access patterns
- Transpose a matrix to convert column access to row access
- Use `@simd` with `Vec4f`/`Vec8f` for CPU vectorization comparison
