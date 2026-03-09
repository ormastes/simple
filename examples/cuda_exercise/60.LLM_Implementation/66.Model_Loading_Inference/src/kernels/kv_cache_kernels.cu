/**
 * @file kv_cache_kernels.cu
 * @brief CUDA kernels for KV cache management
 *
 * Provides GPU kernels for efficiently managing the key-value cache used
 * during autoregressive inference. The cache stores previously computed
 * key and value projections so they do not need to be recomputed at each
 * generation step.
 *
 * Two core operations:
 * - Append: add new K/V entries at the current position
 * - Rotate: shift cache contents for sliding window attention
 */

#include "common/inference_engine.h"
#include "cuda_utils.h"

namespace llm {

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Append new key/value entries to the cache
 *
 * Copies new_tokens worth of K or V data into the cache at the current
 * position. Each thread handles one element of the d_model dimension.
 *
 * @param[out] cache       Cache buffer [max_seq_len, d]
 * @param[in]  new_data    New entries to append [num_new, d]
 * @param[in]  current_len Current number of cached positions
 * @param[in]  num_new     Number of new tokens to append
 * @param[in]  d           Feature dimension (num_heads * head_dim)
 * @param[in]  max_len     Maximum cache capacity
 */
__global__ void kv_cache_append_kernel(
    float* cache, const float* new_data,
    int current_len, int num_new, int d, int max_len
) {
    int token_idx = blockIdx.x;  // Which new token [0, num_new)
    int dim_idx = threadIdx.x;   // Which dimension [0, d)

    if (token_idx < num_new && dim_idx < d) {
        int cache_pos = current_len + token_idx;
        if (cache_pos < max_len) {
            cache[cache_pos * d + dim_idx] =
                new_data[token_idx * d + dim_idx];
        }
    }
}

/**
 * @brief Rotate (shift left) the KV cache for sliding window attention
 *
 * When the cache is full, this kernel shifts all entries left by `shift`
 * positions, discarding the oldest entries and making room for new ones.
 *
 * @param[in,out] cache       Cache buffer [max_seq_len, d]
 * @param[in]     shift       Number of positions to shift left
 * @param[in]     current_len Current cache length before rotation
 * @param[in]     d           Feature dimension
 * @param[in]     max_len     Maximum cache capacity
 */
__global__ void kv_cache_rotate_kernel(
    float* cache, int shift, int current_len, int d, int max_len
) {
    int pos_idx = blockIdx.x;    // Destination position
    int dim_idx = threadIdx.x;   // Dimension index

    int src_pos = pos_idx + shift;
    int remaining = current_len - shift;

    if (pos_idx < remaining && src_pos < current_len && dim_idx < d) {
        cache[pos_idx * d + dim_idx] =
            cache[src_pos * d + dim_idx];
    }
}

// ============================================================================
// Launch wrappers
// ============================================================================

/**
 * @brief Append new K/V entries to the cache for a specific layer
 *
 * Launches the append kernel for both key and value caches, then
 * updates the position counter after the last layer is processed.
 */
void kv_cache_append(KVCache& cache, const float* new_keys, const float* new_values,
                    int layer_idx, int num_new, cudaStream_t stream) {
    if (num_new <= 0 || layer_idx < 0 || layer_idx >= cache.num_layers) return;

    int d = cache.num_heads * cache.head_dim;
    size_t layer_offset = static_cast<size_t>(layer_idx) * cache.max_seq_len * d;

    int block_dim = (d <= 1024) ? d : 1024;

    kv_cache_append_kernel<<<num_new, block_dim, 0, stream>>>(
        cache.d_key_cache + layer_offset, new_keys,
        cache.current_len, num_new, d, cache.max_seq_len);

    kv_cache_append_kernel<<<num_new, block_dim, 0, stream>>>(
        cache.d_value_cache + layer_offset, new_values,
        cache.current_len, num_new, d, cache.max_seq_len);

    // Update position counter (only once, after the last layer)
    if (layer_idx == cache.num_layers - 1) {
        cache.current_len += num_new;
    }
}

/**
 * @brief Rotate the cache for sliding window attention
 *
 * Shifts entries left by the specified amount and updates the position counter.
 */
void kv_cache_rotate(KVCache& cache, int layer_idx, int shift, cudaStream_t stream) {
    if (shift <= 0 || layer_idx < 0 || layer_idx >= cache.num_layers) return;
    if (shift >= cache.current_len) {
        // Shift is larger than cache contents; just reset
        cache.current_len = 0;
        return;
    }

    int d = cache.num_heads * cache.head_dim;
    size_t layer_offset = static_cast<size_t>(layer_idx) * cache.max_seq_len * d;
    int remaining = cache.current_len - shift;

    int block_dim = (d <= 1024) ? d : 1024;

    kv_cache_rotate_kernel<<<remaining, block_dim, 0, stream>>>(
        cache.d_key_cache + layer_offset, shift,
        cache.current_len, d, cache.max_seq_len);

    kv_cache_rotate_kernel<<<remaining, block_dim, 0, stream>>>(
        cache.d_value_cache + layer_offset, shift,
        cache.current_len, d, cache.max_seq_len);

    // Update position counter (only once, after the last layer)
    if (layer_idx == cache.num_layers - 1) {
        cache.current_len = remaining;
    }
}

} // namespace llm
