/**
 * @file 01_naive.cu
 * @brief Naive attention implementation materializing the full attention matrix.
 *
 * Computes scaled dot-product attention: Attention(Q,K,V) = softmax(QK^T / sqrt(d)) * V
 * by first materializing the full NxN attention score matrix, applying softmax row-wise,
 * then multiplying by V. Memory usage is O(N^2) which limits maximum sequence length.
 */

#include "attention/01_naive.h"
#include <cuda_runtime.h>
#include <cmath>
#include <cfloat>

namespace opt78 {

/**
 * @brief Compute QK^T / sqrt(d_k) and store full attention scores.
 *
 * @param[out] scores [batch x seq_len x seq_len]
 * @param[in]  Q      [batch x seq_len x head_dim]
 * @param[in]  K      [batch x seq_len x head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Head dimension
 * @param[in]  scale   1.0 / sqrt(head_dim)
 */
__global__ void compute_scores_kernel(float* __restrict__ scores,
                                       const float* __restrict__ Q,
                                       const float* __restrict__ K,
                                       int seq_len, int head_dim, float scale) {
    int batch_idx = blockIdx.z;
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < seq_len && col < seq_len) {
        const float* q_row = Q + batch_idx * seq_len * head_dim + row * head_dim;
        const float* k_col = K + batch_idx * seq_len * head_dim + col * head_dim;

        float dot = 0.0f;
        for (int d = 0; d < head_dim; ++d) {
            dot += q_row[d] * k_col[d];
        }

        scores[batch_idx * seq_len * seq_len + row * seq_len + col] = dot * scale;
    }
}

/**
 * @brief Row-wise softmax of the attention scores.
 *
 * Numerically stable softmax: subtract max before exponentiation.
 *
 * @param[in,out] scores [batch x seq_len x seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void softmax_kernel(float* __restrict__ scores,
                                int seq_len) {
    int batch_idx = blockIdx.y;
    int row = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < seq_len) {
        float* row_ptr = scores + batch_idx * seq_len * seq_len + row * seq_len;

        // Find max for numerical stability
        float max_val = -FLT_MAX;
        for (int j = 0; j < seq_len; ++j) {
            max_val = fmaxf(max_val, row_ptr[j]);
        }

        // Compute exp and sum
        float sum = 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            row_ptr[j] = expf(row_ptr[j] - max_val);
            sum += row_ptr[j];
        }

        // Normalize
        float inv_sum = 1.0f / sum;
        for (int j = 0; j < seq_len; ++j) {
            row_ptr[j] *= inv_sum;
        }
    }
}

/**
 * @brief Multiply attention weights by V: output = attn_weights * V
 *
 * @param[out] output  [batch x seq_len x head_dim]
 * @param[in]  weights [batch x seq_len x seq_len]
 * @param[in]  V       [batch x seq_len x head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Head dimension
 */
__global__ void attn_value_kernel(float* __restrict__ output,
                                   const float* __restrict__ weights,
                                   const float* __restrict__ V,
                                   int seq_len, int head_dim) {
    int batch_idx = blockIdx.z;
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < seq_len && col < head_dim) {
        const float* w_row = weights + batch_idx * seq_len * seq_len + row * seq_len;
        float sum = 0.0f;
        for (int k = 0; k < seq_len; ++k) {
            sum += w_row[k] * V[batch_idx * seq_len * head_dim + k * head_dim + col];
        }
        output[batch_idx * seq_len * head_dim + row * head_dim + col] = sum;
    }
}

void attention_naive(float* output, float* scores_buf,
                     const float* Q, const float* K, const float* V,
                     int batch, int seq_len, int head_dim,
                     cudaStream_t s) {
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));

    dim3 block(16, 16);

    // Step 1: Compute QK^T / sqrt(d)
    {
        dim3 grid((seq_len + block.x - 1) / block.x,
                  (seq_len + block.y - 1) / block.y,
                  batch);
        compute_scores_kernel<<<grid, block, 0, s>>>(scores_buf, Q, K, seq_len, head_dim, scale);
    }

    // Step 2: Softmax
    {
        int threads = 256;
        dim3 grid_sm((seq_len + threads - 1) / threads, batch);
        softmax_kernel<<<grid_sm, threads, 0, s>>>(scores_buf, seq_len);
    }

    // Step 3: Multiply by V
    {
        dim3 grid((head_dim + block.x - 1) / block.x,
                  (seq_len + block.y - 1) / block.y,
                  batch);
        attn_value_kernel<<<grid, block, 0, s>>>(output, scores_buf, V, seq_len, head_dim);
    }
}

}  // namespace opt78
