/**
 * @file 02_tiled.h
 * @brief Tiled attention with shared memory for QK^T and value multiplication.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Tiled attention with shared memory optimizations.
 *
 * Uses shared memory tiling for the QK^T score computation and the
 * attention-value multiplication. Softmax uses parallel reduction.
 * Still materializes the full attention matrix.
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
 */
void attention_tiled(float* output, float* scores_buf,
                     const float* Q, const float* K, const float* V,
                     int batch, int seq_len, int head_dim,
                     cudaStream_t s = 0);

}  // namespace opt78
