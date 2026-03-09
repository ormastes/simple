/**
 * @file causal_mask.cuh
 * @brief Causal masking predicate for autoregressive attention
 */
#pragma once
#include <cuda_runtime.h>
#include <cfloat>

namespace transformer {

/**
 * @brief Check if position k should attend to position q (causal/lower-triangular)
 * @param[in] q Query position (row)
 * @param[in] k Key position (column)
 * @return true if k <= q (causal attention allows attending to current and past)
 */
__device__ __forceinline__ bool causal_keep(int q, int k) {
    return k <= q;
}

/**
 * @brief Apply causal mask to attention score
 * @param[in] score Raw attention score
 * @param[in] q Query position
 * @param[in] k Key position
 * @return score if causal_keep(q,k), else -inf
 */
__device__ __forceinline__ float apply_causal_mask(float score, int q, int k) {
    return causal_keep(q, k) ? score : -FLT_MAX;
}

/**
 * @brief Generate causal mask value for a tile
 * @param[in] q_start Start of query tile
 * @param[in] k_start Start of key tile
 * @param[in] q_offset Offset within query tile
 * @param[in] k_offset Offset within key tile
 * @return true if the position should be kept (not masked)
 */
__device__ __forceinline__ bool tile_causal_keep(int q_start, int k_start, int q_offset, int k_offset) {
    return (k_start + k_offset) <= (q_start + q_offset);
}

/**
 * @brief Check if an entire key tile is fully masked (optimization)
 *
 * If q_end < k_start, all entries in this tile are masked and can be skipped.
 *
 * @param[in] q_start Start of query tile
 * @param[in] q_size Number of rows in query tile
 * @param[in] k_start Start of key tile
 * @return true if the entire tile is masked
 */
__device__ __forceinline__ bool tile_fully_masked(int q_start, int q_size, int k_start) {
    return k_start > (q_start + q_size - 1);
}

/**
 * @brief Check if an entire key tile is fully unmasked
 *
 * If q_start >= k_end, all entries are valid and no per-element masking is needed.
 *
 * @param[in] q_start Start of query tile
 * @param[in] k_start Start of key tile
 * @param[in] k_size Number of columns in key tile
 * @return true if all positions in the tile are unmasked
 */
__device__ __forceinline__ bool tile_fully_unmasked(int q_start, int k_start, int k_size) {
    return q_start >= (k_start + k_size - 1);
}

} // namespace transformer
