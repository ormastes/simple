/**
 * @file 01_naive.h
 * @brief Naive attention - materializes full NxN attention matrix.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Naive scaled dot-product attention.
 *
 * Materializes the full seq_len x seq_len attention score matrix, applies
 * row-wise softmax, then multiplies by V. Memory usage is O(batch * seq_len^2).
 *
 * @param[out] output      [batch x seq_len x head_dim] (device)
 * @param[out] scores_buf  [batch x seq_len x seq_len] scratch buffer (device)
 * @param[in]  Q           [batch x seq_len x head_dim] (device)
 * @param[in]  K           [batch x seq_len x head_dim] (device)
 * @param[in]  V           [batch x seq_len x head_dim] (device)
 * @param[in]  batch       Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Head dimension
 * @param[in]  s           CUDA stream (default 0)
 *
 * @warning Requires O(N^2) memory for the score matrix
 */
void attention_naive(float* output, float* scores_buf,
                     const float* Q, const float* K, const float* V,
                     int batch, int seq_len, int head_dim,
                     cudaStream_t s = 0);

}  // namespace opt78
