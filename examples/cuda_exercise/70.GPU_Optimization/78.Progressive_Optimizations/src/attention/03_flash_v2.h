/**
 * @file 03_flash_v2.h
 * @brief FlashAttention v2 style - online softmax, O(N) memory.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief FlashAttention v2: online softmax without materializing the NxN matrix.
 *
 * Computes exact scaled dot-product attention using the FlashAttention algorithm.
 * Processes K/V in tiles with online softmax, requiring only O(N) additional memory
 * instead of O(N^2). No scratch buffer needed.
 *
 * @param[out] output   [batch x seq_len x head_dim] (device)
 * @param[in]  Q        [batch x seq_len x head_dim] (device)
 * @param[in]  K        [batch x seq_len x head_dim] (device)
 * @param[in]  V        [batch x seq_len x head_dim] (device)
 * @param[in]  batch    Batch size
 * @param[in]  seq_len  Sequence length
 * @param[in]  head_dim Head dimension (max 128)
 * @param[in]  s        CUDA stream (default 0)
 *
 * @note head_dim is clamped to 128 internally for register usage
 */
void attention_flash_v2(float* output,
                        const float* Q, const float* K, const float* V,
                        int batch, int seq_len, int head_dim,
                        cudaStream_t s = 0);

}  // namespace opt78
