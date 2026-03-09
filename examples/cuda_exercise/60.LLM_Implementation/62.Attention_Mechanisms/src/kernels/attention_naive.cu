/**
 * @file attention_naive.cu
 * @brief Naive CUDA implementation of scaled dot-product attention
 *
 * Implements self_attention_forward and causal_attention_forward as
 * reference implementations. These kernels prioritize clarity and
 * correctness over performance; optimized versions would use tiling,
 * FlashAttention-style fusion, or cuBLAS for the matmuls.
 */

#include "common/self_attention.h"
#include "common/causal_attention.h"
#include "cuda_utils.h"
#include <cmath>
#include <cfloat>

namespace llm {

/**
 * @brief Compute QK^T scores for one head, one batch element
 *
 * scores[i][j] = sum_k Q[i][k] * K[j][k] / sqrt(head_dim)
 *
 * @param[out] scores  Output scores [seq_len, seq_len]
 * @param[in]  Q       Query for one head [seq_len, head_dim]
 * @param[in]  K       Key for one head [seq_len, head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Dimension per head
 * @param[in]  scale   Scaling factor (1/sqrt(head_dim))
 */
__global__ void compute_attention_scores_kernel(
    float* scores,
    const float* Q,
    const float* K,
    int seq_len,
    int head_dim,
    float scale
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;  // query position
    int col = blockIdx.y * blockDim.y + threadIdx.y;  // key position

    if (row < seq_len && col < seq_len) {
        float dot = 0.0f;
        for (int k = 0; k < head_dim; ++k) {
            dot += Q[row * head_dim + k] * K[col * head_dim + k];
        }
        scores[row * seq_len + col] = dot * scale;
    }
}

/**
 * @brief Apply causal mask: set scores[i][j] = -inf where j > i
 *
 * @param[in,out] scores  Attention scores [seq_len, seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void apply_causal_mask_kernel(
    float* scores,
    int seq_len
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < seq_len && col < seq_len) {
        if (col > row) {
            scores[row * seq_len + col] = -FLT_MAX;
        }
    }
}

/**
 * @brief Row-wise softmax over attention scores
 *
 * For numerical stability, subtracts the row maximum before exponentiating.
 *
 * @param[in,out] scores  Attention scores [seq_len, seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void softmax_rows_kernel(
    float* scores,
    int seq_len
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < seq_len) {
        // Find row max for numerical stability
        float max_val = -FLT_MAX;
        for (int j = 0; j < seq_len; ++j) {
            float val = scores[row * seq_len + j];
            if (val > max_val) max_val = val;
        }

        // Compute exp and sum
        float sum = 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            float exp_val = expf(scores[row * seq_len + j] - max_val);
            scores[row * seq_len + j] = exp_val;
            sum += exp_val;
        }

        // Normalize
        float inv_sum = (sum > 0.0f) ? (1.0f / sum) : 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            scores[row * seq_len + j] *= inv_sum;
        }
    }
}

/**
 * @brief Multiply attention weights by V: output = attn_weights * V
 *
 * @param[out] output      Output [seq_len, head_dim]
 * @param[in]  attn_weights Attention weights after softmax [seq_len, seq_len]
 * @param[in]  V           Value tensor [seq_len, head_dim]
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Dimension per head
 */
__global__ void attention_value_multiply_kernel(
    float* output,
    const float* attn_weights,
    const float* V,
    int seq_len,
    int head_dim
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;  // query position
    int dim = blockIdx.y * blockDim.y + threadIdx.y;   // head dimension

    if (row < seq_len && dim < head_dim) {
        float sum = 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            sum += attn_weights[row * seq_len + j] * V[j * head_dim + dim];
        }
        output[row * head_dim + dim] = sum;
    }
}

/**
 * @brief Internal helper: compute attention for all heads
 *
 * Processes the Q, K, V tensors which are laid out as [batch, seq_len, d_model].
 * Splits into heads, computes attention per head, and writes back concatenated output.
 *
 * @param output     [batch, seq_len, d_model]
 * @param Q          [batch, seq_len, d_model]
 * @param K          [batch, seq_len, d_model]
 * @param V          [batch, seq_len, d_model]
 * @param config     Attention configuration
 * @param batch_size Batch size
 * @param seq_len    Sequence length
 * @param causal     Whether to apply causal masking
 * @param stream     CUDA stream
 */
static void attention_forward_impl(float* output, const float* Q, const float* K, const float* V,
                                   const AttentionConfig& config, int batch_size, int seq_len,
                                   bool causal, cudaStream_t stream) {
    int num_heads = config.num_heads;
    int head_dim = config.head_dim;
    int d_model = config.d_model;
    float scale = 1.0f / std::sqrt(static_cast<float>(head_dim));

    // Allocate temporary storage for scores [seq_len, seq_len]
    float* d_scores = nullptr;
    CHECK_CUDA(cudaMalloc(&d_scores, seq_len * seq_len * sizeof(float)));

    // Allocate temp storage for per-head Q, K, V slices [seq_len, head_dim]
    float* d_Q_head = nullptr;
    float* d_K_head = nullptr;
    float* d_V_head = nullptr;
    float* d_out_head = nullptr;
    CHECK_CUDA(cudaMalloc(&d_Q_head, seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_K_head, seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_V_head, seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out_head, seq_len * head_dim * sizeof(float)));

    // Grid/block dimensions for score computation
    dim3 score_block(16, 16);
    dim3 score_grid((seq_len + 15) / 16, (seq_len + 15) / 16);

    // Grid/block for softmax (one thread per row)
    int softmax_threads = 256;
    int softmax_blocks = (seq_len + softmax_threads - 1) / softmax_threads;

    // Grid/block for value multiply
    dim3 val_block(16, 16);
    dim3 val_grid((seq_len + 15) / 16, (head_dim + 15) / 16);

    for (int b = 0; b < batch_size; ++b) {
        for (int h = 0; h < num_heads; ++h) {
            // Extract head h from Q, K, V
            // Q layout: [batch, seq_len, d_model] where d_model = num_heads * head_dim
            // Head h corresponds to columns [h*head_dim, (h+1)*head_dim)
            // We need to gather strided data into contiguous per-head buffers

            // Copy per-head data: extract columns [h*head_dim .. (h+1)*head_dim)
            // from each row of the [seq_len, d_model] slice for batch b
            for (int s = 0; s < seq_len; ++s) {
                int src_offset = (b * seq_len + s) * d_model + h * head_dim;
                int dst_offset = s * head_dim;
                CHECK_CUDA(cudaMemcpyAsync(d_Q_head + dst_offset, Q + src_offset,
                                           head_dim * sizeof(float),
                                           cudaMemcpyDeviceToDevice, stream));
                CHECK_CUDA(cudaMemcpyAsync(d_K_head + dst_offset, K + src_offset,
                                           head_dim * sizeof(float),
                                           cudaMemcpyDeviceToDevice, stream));
                CHECK_CUDA(cudaMemcpyAsync(d_V_head + dst_offset, V + src_offset,
                                           head_dim * sizeof(float),
                                           cudaMemcpyDeviceToDevice, stream));
            }

            // Compute QK^T / sqrt(head_dim)
            compute_attention_scores_kernel<<<score_grid, score_block, 0, stream>>>(
                d_scores, d_Q_head, d_K_head, seq_len, head_dim, scale);

            // Apply causal mask if requested
            if (causal) {
                apply_causal_mask_kernel<<<score_grid, score_block, 0, stream>>>(
                    d_scores, seq_len);
            }

            // Softmax
            softmax_rows_kernel<<<softmax_blocks, softmax_threads, 0, stream>>>(
                d_scores, seq_len);

            // Multiply by V
            attention_value_multiply_kernel<<<val_grid, val_block, 0, stream>>>(
                d_out_head, d_scores, d_V_head, seq_len, head_dim);

            // Scatter output back into [batch, seq_len, d_model]
            for (int s = 0; s < seq_len; ++s) {
                int dst_offset = (b * seq_len + s) * d_model + h * head_dim;
                int src_offset = s * head_dim;
                CHECK_CUDA(cudaMemcpyAsync(output + dst_offset, d_out_head + src_offset,
                                           head_dim * sizeof(float),
                                           cudaMemcpyDeviceToDevice, stream));
            }
        }
    }

    CHECK_CUDA(cudaStreamSynchronize(stream));

    // Clean up temporaries
    cudaFree(d_scores);
    cudaFree(d_Q_head);
    cudaFree(d_K_head);
    cudaFree(d_V_head);
    cudaFree(d_out_head);
}

void self_attention_forward(float* output, const float* Q, const float* K, const float* V,
                           const AttentionConfig& config, int batch_size, int seq_len,
                           cudaStream_t stream) {
    attention_forward_impl(output, Q, K, V, config, batch_size, seq_len,
                          /*causal=*/false, stream);
}

void causal_attention_forward(float* output, const float* Q, const float* K, const float* V,
                             const AttentionConfig& config, int batch_size, int seq_len,
                             cudaStream_t stream) {
    attention_forward_impl(output, Q, K, V, config, batch_size, seq_len,
                          /*causal=*/true, stream);
}

} // namespace llm
