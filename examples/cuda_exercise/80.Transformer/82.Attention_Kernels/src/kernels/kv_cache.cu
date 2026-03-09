/**
 * @file kv_cache.cu
 * @brief KV cache management kernels for autoregressive inference
 *
 * During autoregressive generation, previously computed key and value tensors are
 * cached to avoid redundant computation. This module provides kernels to append
 * newly generated KV pairs to the cache and to read cached entries for use in
 * attention computation.
 */
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Append new KV pairs to the cache at a given offset
 *
 * Copies new_kv entries into the cache starting at cache_offset along the
 * sequence dimension. The cache and new_kv share the same [num_heads, head_dim]
 * layout for each token position.
 *
 * @param[in,out] cache        KV cache [max_seq_len, num_heads, head_dim]
 * @param[in]     new_kv       New KV pairs [num_new, num_heads, head_dim]
 * @param[in]     cache_offset Starting position in the cache sequence dimension
 * @param[in]     num_new      Number of new tokens to append
 * @param[in]     num_heads    Number of attention heads
 * @param[in]     head_dim     Dimension per head
 */
__global__ void kv_cache_append_kernel(float* cache, const float* new_kv,
                                        int cache_offset, int num_new,
                                        int num_heads, int head_dim) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total = num_new * num_heads * head_dim;
    if (idx >= total) return;

    int d = idx % head_dim;
    int h = (idx / head_dim) % num_heads;
    int t = idx / (head_dim * num_heads);

    int cache_idx = (cache_offset + t) * (num_heads * head_dim) + h * head_dim + d;
    cache[cache_idx] = new_kv[idx];
}

/**
 * @brief Read KV cache entries for attention computation
 *
 * Copies the first seq_len entries from the cache into a contiguous output buffer.
 *
 * @param[out] output   Output buffer [seq_len, num_heads, head_dim]
 * @param[in]  cache    KV cache [max_seq_len, num_heads, head_dim]
 * @param[in]  seq_len  Number of entries to read from cache
 * @param[in]  num_heads Number of attention heads
 * @param[in]  head_dim Dimension per head
 */
__global__ void kv_cache_read_kernel(float* output, const float* cache,
                                      int seq_len, int num_heads, int head_dim) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total = seq_len * num_heads * head_dim;
    if (idx >= total) return;
    output[idx] = cache[idx];
}

/**
 * @brief Launch kernel to append new KV pairs to cache
 *
 * @param[in,out] cache        KV cache buffer
 * @param[in]     new_kv       New KV pairs to append
 * @param[in]     cache_offset Starting sequence position in cache
 * @param[in]     num_new      Number of new tokens
 * @param[in]     num_heads    Number of attention heads
 * @param[in]     head_dim     Head dimension
 * @param[in]     stream       CUDA stream
 */
void launch_kv_cache_append(float* cache, const float* new_kv,
                            int cache_offset, int num_new,
                            int num_heads, int head_dim, cudaStream_t stream) {
    int total = num_new * num_heads * head_dim;
    int block = 256;
    int grid = (total + block - 1) / block;
    kv_cache_append_kernel<<<grid, block, 0, stream>>>(cache, new_kv, cache_offset,
                                                        num_new, num_heads, head_dim);
}

/**
 * @brief Launch kernel to read KV cache entries
 *
 * @param[out] output   Output buffer
 * @param[in]  cache    KV cache buffer
 * @param[in]  seq_len  Number of positions to read
 * @param[in]  num_heads Number of attention heads
 * @param[in]  head_dim Head dimension
 * @param[in]  stream   CUDA stream
 */
void launch_kv_cache_read(float* output, const float* cache,
                          int seq_len, int num_heads, int head_dim, cudaStream_t stream) {
    int total = seq_len * num_heads * head_dim;
    int block = 256;
    int grid = (total + block - 1) / block;
    kv_cache_read_kernel<<<grid, block, 0, stream>>>(output, cache, seq_len, num_heads, head_dim);
}

} // namespace transformer
