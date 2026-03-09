# Part 82: Attention Kernels

**Goal**: Implement fused scaled dot-product attention (FlashAttention-style), rotary position embeddings (RoPE), KV cache management, and standalone softmax as pure CUDA kernels for transformer inference.

## Project Structure

```
82.Attention_Kernels/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   └── kernels/
│       ├── flash_attention.cu
│       ├── rope.cu
│       ├── kv_cache.cu
│       └── softmax.cu
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_flash_attention.cu
            ├── test_rope.cu
            ├── test_kv_cache.cu
            └── test_softmax.cu
```

## Quick Navigation

- [82.1 Softmax](#821-softmax)
- [82.2 Rotary Position Embeddings (RoPE)](#822-rotary-position-embeddings-rope)
- [82.3 KV Cache](#823-kv-cache)
- [82.4 FlashAttention](#824-flashattention)
- [82.5 Summary](#825-summary)
- [Build & Run](#build--run)

---

## **82.1 Softmax**

The softmax kernel provides a standalone, numerically stable row-wise softmax for use outside of fused attention contexts (e.g., for classification heads or standalone normalization).

### **82.1.1 Algorithm**

The kernel uses the standard three-phase approach with warp-level shuffle reductions for parallel computation across threads within a block.

1. **Find row maximum** using warp `__shfl_xor_sync` reduction across all threads, then cross-warp reduction via shared memory.
2. **Compute exp(x - max)** and accumulate the sum using the same reduction strategy.
3. **Normalize** each element by dividing by the sum.

### **82.1.2 Implementation**

```cpp
// softmax.cu - Row-wise softmax with warp shuffle reductions
__global__ void softmax_kernel(float* output, const float* input, int rows, int cols) {
    // Each block handles one row
    // Phase 1: find max via warp shuffle + shared memory
    // Phase 2: compute exp(x - max) and sum
    // Phase 3: normalize by 1/sum
}
```

**Key Points**:
- One block per row ensures coalesced memory access within each row
- Warp shuffle reductions avoid unnecessary shared memory traffic for intra-warp communication
- Subtracting the row maximum before exponentiation prevents overflow with large logits

**Source**: `src/kernels/softmax.cu`

### **82.1.3 Practical Usage**

```cpp
transformer::launch_softmax(d_output, d_input, rows, cols, stream);
// Each row of d_output sums to 1.0, no NaN/Inf even with extreme input values
```

---

## **82.2 Rotary Position Embeddings (RoPE)**

RoPE encodes positional information by applying position-dependent rotations to pairs of query/key dimensions, enabling the attention dot product to naturally capture relative positions.

### **82.2.1 Algorithm**

For each pair of dimensions `(d, d + half_dim)` at sequence position `t`:

```
freq = 1 / theta_base^(2d / head_dim)
angle = t * freq
x'[d]            = x[d] * cos(angle) - x[d+half] * sin(angle)
x'[d+half]       = x[d] * sin(angle) + x[d+half] * cos(angle)
```

The base frequency `theta_base` (typically 10000.0) controls how quickly different dimension pairs rotate. Lower-indexed dimensions rotate faster, capturing fine-grained positional differences, while higher-indexed dimensions rotate slowly for long-range position encoding.

### **82.2.2 Implementation**

```cpp
// rope.cu - In-place rotary position embedding
__global__ void rope_kernel(float* x, int seq_len, int num_heads,
                            int head_dim, float theta_base) {
    // Each thread handles one (batch, position, head, dimension_pair)
    // Computes angle = t * freq, applies 2D rotation to the pair
}
```

**Key Points**:
- In-place operation to minimize memory allocation
- Each thread independently processes one dimension pair -- no inter-thread communication needed
- Position 0 produces identity (angle = 0, cos = 1, sin = 0)
- Rotation preserves vector L2 norms (orthogonal transformation)

**Source**: `src/kernels/rope.cu`

### **82.2.3 Practical Usage**

```cpp
// Apply RoPE to queries and keys before attention
transformer::launch_rope(d_queries, batch, seq_len, num_heads, head_dim, 10000.0f, stream);
transformer::launch_rope(d_keys, batch, seq_len, num_heads, head_dim, 10000.0f, stream);
```

---

## **82.3 KV Cache**

During autoregressive generation, previously computed key and value tensors are cached to avoid recomputing them for each new token. The KV cache kernels manage appending new entries and reading cached data.

### **82.3.1 Cache Layout**

The cache uses a `[max_seq_len, num_heads, head_dim]` layout, where `max_seq_len` is the maximum sequence length supported. New tokens are appended at a monotonically increasing offset.

### **82.3.2 Operations**

- **Append**: Copy new KV pairs into the cache at a given sequence offset.
- **Read**: Extract the first `seq_len` entries from the cache for attention computation.

### **82.3.3 Implementation**

```cpp
// kv_cache.cu - Cache management for autoregressive inference
__global__ void kv_cache_append_kernel(float* cache, const float* new_kv,
                                        int cache_offset, int num_new,
                                        int num_heads, int head_dim);

__global__ void kv_cache_read_kernel(float* output, const float* cache,
                                      int seq_len, int num_heads, int head_dim);
```

**Key Points**:
- Simple element-wise copy with index remapping for the cache offset
- Separate caches are maintained for keys and values (call the functions twice)
- No synchronization overhead -- each element is independently mapped

**Source**: `src/kernels/kv_cache.cu`

### **82.3.4 Practical Usage**

```cpp
// During generation step t:
transformer::launch_kv_cache_append(d_k_cache, d_new_keys, t, 1, num_heads, head_dim, stream);
transformer::launch_kv_cache_append(d_v_cache, d_new_values, t, 1, num_heads, head_dim, stream);

// Read full cache for attention
transformer::launch_kv_cache_read(d_keys, d_k_cache, t + 1, num_heads, head_dim, stream);
transformer::launch_kv_cache_read(d_values, d_v_cache, t + 1, num_heads, head_dim, stream);
```

---

## **82.4 FlashAttention**

The FlashAttention kernel implements tiled scaled dot-product attention (SDPA) using online softmax to avoid materializing the full N x N attention matrix.

### **82.4.1 Algorithm Overview**

Standard SDPA computes `O = softmax(QK^T / sqrt(d)) * V`, which requires O(N^2) memory for the attention matrix. FlashAttention avoids this by:

1. Processing K/V in tiles of size `FA_TILE_SIZE`
2. Maintaining a running softmax state (max, sum of exponentials) across tiles
3. Rescaling accumulated PV products when the running maximum changes
4. Normalizing only once at the end

### **82.4.2 Online Softmax**

The key insight is that softmax can be computed incrementally. When a new tile introduces a larger maximum:

```
new_max = max(old_max, tile_max)
old_accumulators *= exp(old_max - new_max)    // rescale
sum_exp = sum_exp * exp(old_max - new_max) + sum(exp(tile_scores - new_max))
```

This ensures numerical stability throughout the tiled computation.

### **82.4.3 Implementation**

```cpp
// flash_attention.cu - Tiled SDPA with online softmax
__global__ void sdpa_tiled_kernel(float* output, const float* Q, const float* K,
                                   const float* V, int seq_len, int head_dim,
                                   float scale, bool causal) {
    // One block per query position
    // Iterates over key tiles, computes QK^T scores
    // Online softmax maintains running max and sum
    // Accumulates weighted value vectors
}
```

**Key Points**:
- Memory complexity reduced from O(N^2) to O(N * tile_size)
- Supports causal masking by limiting the key range to `[0, q_idx + 1)`
- Current implementation uses a simplified single-thread accumulation for clarity
- Launched per (batch, head) pair to handle multi-head attention

**Source**: `src/kernels/flash_attention.cu`

### **82.4.4 Practical Usage**

```cpp
// Full multi-head attention
transformer::launch_flash_attention(d_output, d_Q, d_K, d_V,
                                     batch, num_heads, seq_len, head_dim,
                                     /*causal=*/true, stream);
```

---

## **82.5 Summary**

- **Key Takeaways**:
  - Softmax uses warp shuffle reductions for efficient parallel row-wise normalization
  - RoPE applies orthogonal rotations preserving norms, encoding relative positions
  - KV cache enables O(1) per-token append during autoregressive generation
  - FlashAttention reduces attention memory from O(N^2) to O(N) via tiled online softmax

- **Performance Characteristics**:
  - Softmax: bandwidth-bound for small rows, compute-bound for large rows
  - RoPE: fully parallel, no inter-thread communication, trivially scalable
  - KV Cache: pure memory copy, limited by memory bandwidth
  - FlashAttention: memory-efficient but current simplified implementation is not optimized for throughput

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | NaN in softmax output | Overflow in exp() | Subtract row maximum before exponentiation (already implemented) |
  | Wrong attention output | Missing scale factor | Ensure `1/sqrt(head_dim)` scaling is applied to QK^T scores |
  | KV cache corruption | Wrong offset | Track cache offset carefully; offset = number of previously generated tokens |
  | RoPE dimension mismatch | Odd head_dim | head_dim must be even for RoPE (pairs of dimensions) |

- **Next Steps**: Integrate with [83.MLP](../83.MLP/README.md) for complete transformer block, or optimize the FlashAttention kernel with multi-thread accumulation and shared memory tiling.

- **References**:
  - [FlashAttention: Fast and Memory-Efficient Exact Attention](https://arxiv.org/abs/2205.05141)
  - [RoFormer: Enhanced Transformer with Rotary Position Embedding](https://arxiv.org/abs/2104.09864)
  - [Multi-Query Attention / Grouped-Query Attention](https://arxiv.org/abs/2305.13245)

---

## Build & Run

From the repository build directory:

```bash
# Build
ninja 82_Attention_Kernels_test

# Run tests
./80.Transformer/82.Attention_Kernels/82_Attention_Kernels_test

# Generate documentation
ninja doxygen_82_Attention_Kernels
```
