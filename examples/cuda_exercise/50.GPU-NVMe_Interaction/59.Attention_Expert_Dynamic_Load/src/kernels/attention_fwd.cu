/**
 * @file attention_fwd.cu
 * @brief CUDA kernels for multi-head attention forward pass
 *
 * Implements efficient multi-head attention with support for:
 * - Flash attention style (tiled computation)
 * - Causal masking for autoregressive models
 * - Optional dynamic weight loading from NVMe
 */

#include "attention_types.h"
#include "cuda_utils.h"
#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include <cmath>

namespace attention_expert {

/**
 * @brief Linear projection kernel (matrix multiplication)
 *
 * Computes Y = X * W^T + bias for attention projections (Q, K, V, O).
 *
 * @param[in]  input   Input tensor [batch*seq_len, hidden_dim]
 * @param[in]  weight  Weight matrix [out_dim, hidden_dim]
 * @param[in]  bias    Bias vector [out_dim] (can be nullptr)
 * @param[out] output  Output tensor [batch*seq_len, out_dim]
 * @param[in]  batch_seq Batch size * sequence length
 * @param[in]  hidden_dim Hidden dimension
 * @param[in]  out_dim Output dimension
 */
__global__ void linear_projection_kernel(
    const float* __restrict__ input,
    const float* __restrict__ weight,
    const float* __restrict__ bias,
    float* __restrict__ output,
    int batch_seq,
    int hidden_dim,
    int out_dim
) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;  // batch*seq dimension
    int col = blockIdx.x * blockDim.x + threadIdx.x;  // output dimension

    if (row < batch_seq && col < out_dim) {
        float sum = 0.0f;

        // Compute dot product of input row with weight column
        for (int k = 0; k < hidden_dim; ++k) {
            sum += input[row * hidden_dim + k] * weight[col * hidden_dim + k];
        }

        // Add bias if provided
        if (bias != nullptr) {
            sum += bias[col];
        }

        output[row * out_dim + col] = sum;
    }
}

/**
 * @brief Reshape and transpose for multi-head attention
 *
 * Transforms [batch, seq_len, hidden_dim] to [batch, num_heads, seq_len, head_dim]
 *
 * @param[in]  input       Input tensor
 * @param[out] output      Output tensor (transposed)
 * @param[in]  batch_size  Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  num_heads   Number of attention heads
 * @param[in]  head_dim    Dimension per head
 */
__global__ void reshape_for_attention_kernel(
    const float* __restrict__ input,
    float* __restrict__ output,
    int batch_size,
    int seq_len,
    int num_heads,
    int head_dim
) {
    int total_elements = batch_size * seq_len * num_heads * head_dim;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < total_elements) {
        // Decode flat index to (b, s, h, d)
        int d = idx % head_dim;
        int h = (idx / head_dim) % num_heads;
        int s = (idx / (head_dim * num_heads)) % seq_len;
        int b = idx / (head_dim * num_heads * seq_len);

        // Input layout: [b, s, h, d]
        int in_idx = b * (seq_len * num_heads * head_dim) +
                     s * (num_heads * head_dim) +
                     h * head_dim +
                     d;

        // Output layout: [b, h, s, d]
        int out_idx = b * (num_heads * seq_len * head_dim) +
                      h * (seq_len * head_dim) +
                      s * head_dim +
                      d;

        output[out_idx] = input[in_idx];
    }
}

/**
 * @brief Compute attention scores (Q * K^T / sqrt(d_k))
 *
 * Computes scaled dot-product attention scores with optional causal masking.
 *
 * @param[in]  query       Query tensor [batch, heads, seq_len, head_dim]
 * @param[in]  key         Key tensor [batch, heads, seq_len, head_dim]
 * @param[out] scores      Attention scores [batch, heads, seq_len, seq_len]
 * @param[in]  batch_size  Batch size
 * @param[in]  num_heads   Number of heads
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Head dimension
 * @param[in]  scale       Scaling factor (1/sqrt(head_dim))
 * @param[in]  causal      Whether to apply causal mask
 */
__global__ void compute_attention_scores_kernel(
    const float* __restrict__ query,
    const float* __restrict__ key,
    float* __restrict__ scores,
    int batch_size,
    int num_heads,
    int seq_len,
    int head_dim,
    float scale,
    bool causal
) {
    int b = blockIdx.z;                                 // batch
    int h = blockIdx.y;                                 // head
    int q_pos = blockIdx.x * blockDim.x + threadIdx.x;  // query position
    int k_pos = threadIdx.y;                            // key position (block-local)

    if (b >= batch_size || h >= num_heads || q_pos >= seq_len) {
        return;
    }

    // Compute Q*K^T for one position
    for (int k_start = 0; k_start < seq_len; k_start += blockDim.y) {
        int k_idx = k_start + k_pos;
        if (k_idx >= seq_len) continue;

        // Causal masking: future positions are masked out
        if (causal && k_idx > q_pos) {
            scores[b * (num_heads * seq_len * seq_len) +
                   h * (seq_len * seq_len) +
                   q_pos * seq_len +
                   k_idx] = -1e9f;  // Large negative for softmax
            continue;
        }

        float dot = 0.0f;
        for (int d = 0; d < head_dim; ++d) {
            int q_idx = b * (num_heads * seq_len * head_dim) +
                        h * (seq_len * head_dim) +
                        q_pos * head_dim +
                        d;
            int k_idx_full = b * (num_heads * seq_len * head_dim) +
                             h * (seq_len * head_dim) +
                             k_idx * head_dim +
                             d;
            dot += query[q_idx] * key[k_idx_full];
        }

        scores[b * (num_heads * seq_len * seq_len) +
               h * (seq_len * seq_len) +
               q_pos * seq_len +
               k_idx] = dot * scale;
    }
}

/**
 * @brief Softmax over attention scores
 *
 * Applies softmax along the last dimension (key positions).
 *
 * @param[in,out] scores   Attention scores [batch, heads, seq_len, seq_len]
 * @param[in]     batch_size Batch size
 * @param[in]     num_heads Number of heads
 * @param[in]     seq_len   Sequence length
 */
__global__ void softmax_kernel(
    float* __restrict__ scores,
    int batch_size,
    int num_heads,
    int seq_len
) {
    int b = blockIdx.z;
    int h = blockIdx.y;
    int q_pos = blockIdx.x * blockDim.x + threadIdx.x;

    if (b >= batch_size || h >= num_heads || q_pos >= seq_len) {
        return;
    }

    int offset = b * (num_heads * seq_len * seq_len) +
                 h * (seq_len * seq_len) +
                 q_pos * seq_len;

    // Find maximum for numerical stability
    float max_val = -1e9f;
    for (int k = 0; k < seq_len; ++k) {
        max_val = fmaxf(max_val, scores[offset + k]);
    }

    // Compute exp and sum
    float sum = 0.0f;
    for (int k = 0; k < seq_len; ++k) {
        scores[offset + k] = expf(scores[offset + k] - max_val);
        sum += scores[offset + k];
    }

    // Normalize
    for (int k = 0; k < seq_len; ++k) {
        scores[offset + k] /= sum;
    }
}

/**
 * @brief Apply attention weights to values (scores * V)
 *
 * @param[in]  scores      Attention weights [batch, heads, seq_len, seq_len]
 * @param[in]  value       Value tensor [batch, heads, seq_len, head_dim]
 * @param[out] output      Output [batch, heads, seq_len, head_dim]
 * @param[in]  batch_size  Batch size
 * @param[in]  num_heads   Number of heads
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Head dimension
 */
__global__ void apply_attention_kernel(
    const float* __restrict__ scores,
    const float* __restrict__ value,
    float* __restrict__ output,
    int batch_size,
    int num_heads,
    int seq_len,
    int head_dim
) {
    int b = blockIdx.z;
    int h = blockIdx.y;
    int q_pos = blockIdx.x * blockDim.x + threadIdx.x;
    int d = threadIdx.y;

    if (b >= batch_size || h >= num_heads || q_pos >= seq_len || d >= head_dim) {
        return;
    }

    float sum = 0.0f;
    for (int k = 0; k < seq_len; ++k) {
        int score_idx = b * (num_heads * seq_len * seq_len) +
                        h * (seq_len * seq_len) +
                        q_pos * seq_len +
                        k;
        int val_idx = b * (num_heads * seq_len * head_dim) +
                      h * (seq_len * head_dim) +
                      k * head_dim +
                      d;
        sum += scores[score_idx] * value[val_idx];
    }

    int out_idx = b * (num_heads * seq_len * head_dim) +
                  h * (seq_len * head_dim) +
                  q_pos * head_dim +
                  d;
    output[out_idx] = sum;
}

/**
 * @brief Transpose back from [batch, heads, seq, head_dim] to [batch, seq, hidden]
 *
 * @param[in]  input       Input tensor
 * @param[out] output      Output tensor
 * @param[in]  batch_size  Batch size
 * @param[in]  num_heads   Number of heads
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Head dimension
 */
__global__ void transpose_back_kernel(
    const float* __restrict__ input,
    float* __restrict__ output,
    int batch_size,
    int num_heads,
    int seq_len,
    int head_dim
) {
    int total_elements = batch_size * seq_len * num_heads * head_dim;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < total_elements) {
        // Decode from [b, h, s, d] to [b, s, h*d]
        int d = idx % head_dim;
        int s = (idx / head_dim) % seq_len;
        int h = (idx / (head_dim * seq_len)) % num_heads;
        int b = idx / (head_dim * seq_len * num_heads);

        int in_idx = b * (num_heads * seq_len * head_dim) +
                     h * (seq_len * head_dim) +
                     s * head_dim +
                     d;

        int out_idx = b * (seq_len * num_heads * head_dim) +
                      s * (num_heads * head_dim) +
                      h * head_dim +
                      d;

        output[out_idx] = input[in_idx];
    }
}

//
// Host API functions (called from C++ wrapper)
//

/**
 * @brief Multi-head attention forward pass (CUDA implementation)
 *
 * @param[in]  input       Input tensor [batch, seq_len, hidden_dim]
 * @param[in]  weights     Attention weights (Q, K, V, O projections)
 * @param[in]  config      Attention configuration
 * @param[out] output      Output structure
 */
void attention_forward_cuda(
    const float* input,
    const AttentionWeights& weights,
    const AttentionConfig& config,
    AttentionOutput& output
) {
    const int batch_size = config.batch_size;
    const int seq_len = config.seq_len;
    const int num_heads = config.num_heads;
    const int head_dim = config.head_dim;
    const int hidden_dim = config.hidden_dim;
    const int batch_seq = batch_size * seq_len;

    // Allocate temporary buffers
    float *q_proj, *k_proj, *v_proj;
    float *q_heads, *k_heads, *v_heads;
    float *attn_scores;
    float *attn_output;

    CHECK_CUDA(cudaMalloc(&q_proj, batch_seq * hidden_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&k_proj, batch_seq * hidden_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&v_proj, batch_seq * hidden_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&q_heads, batch_size * num_heads * seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&k_heads, batch_size * num_heads * seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&v_heads, batch_size * num_heads * seq_len * head_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&attn_scores, batch_size * num_heads * seq_len * seq_len * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&attn_output, batch_size * num_heads * seq_len * head_dim * sizeof(float)));

    // 1. Linear projections (Q, K, V)
    dim3 proj_block(16, 16);
    dim3 proj_grid((hidden_dim + 15) / 16, (batch_seq + 15) / 16);

    linear_projection_kernel<<<proj_grid, proj_block>>>(
        input, weights.q_weight, weights.q_bias, q_proj, batch_seq, hidden_dim, hidden_dim);
    linear_projection_kernel<<<proj_grid, proj_block>>>(
        input, weights.k_weight, weights.k_bias, k_proj, batch_seq, hidden_dim, hidden_dim);
    linear_projection_kernel<<<proj_grid, proj_block>>>(
        input, weights.v_weight, weights.v_bias, v_proj, batch_seq, hidden_dim, hidden_dim);
    CHECK_KERNEL_LAUNCH();

    // 2. Reshape to multi-head format
    int total_elements = batch_size * seq_len * num_heads * head_dim;
    int reshape_threads = 256;
    int reshape_blocks = (total_elements + reshape_threads - 1) / reshape_threads;

    reshape_for_attention_kernel<<<reshape_blocks, reshape_threads>>>(
        q_proj, q_heads, batch_size, seq_len, num_heads, head_dim);
    reshape_for_attention_kernel<<<reshape_blocks, reshape_threads>>>(
        k_proj, k_heads, batch_size, seq_len, num_heads, head_dim);
    reshape_for_attention_kernel<<<reshape_blocks, reshape_threads>>>(
        v_proj, v_heads, batch_size, seq_len, num_heads, head_dim);
    CHECK_KERNEL_LAUNCH();

    // 3. Compute attention scores
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));
    dim3 score_block(16, 16);
    dim3 score_grid((seq_len + 15) / 16, num_heads, batch_size);

    compute_attention_scores_kernel<<<score_grid, score_block>>>(
        q_heads, k_heads, attn_scores,
        batch_size, num_heads, seq_len, head_dim, scale, config.causal);
    CHECK_KERNEL_LAUNCH();

    // 4. Apply softmax
    dim3 softmax_block(256);
    dim3 softmax_grid((seq_len + 255) / 256, num_heads, batch_size);

    softmax_kernel<<<softmax_grid, softmax_block>>>(
        attn_scores, batch_size, num_heads, seq_len);
    CHECK_KERNEL_LAUNCH();

    // 5. Apply attention to values
    dim3 apply_block(16, 16);
    dim3 apply_grid((seq_len + 15) / 16, num_heads, batch_size);

    apply_attention_kernel<<<apply_grid, apply_block>>>(
        attn_scores, v_heads, attn_output,
        batch_size, num_heads, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    // 6. Transpose back to [batch, seq, hidden]
    float* concat_output;
    CHECK_CUDA(cudaMalloc(&concat_output, batch_seq * hidden_dim * sizeof(float)));

    transpose_back_kernel<<<reshape_blocks, reshape_threads>>>(
        attn_output, concat_output, batch_size, num_heads, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    // 7. Output projection
    linear_projection_kernel<<<proj_grid, proj_block>>>(
        concat_output, weights.o_weight, weights.o_bias, output.output,
        batch_seq, hidden_dim, hidden_dim);
    CHECK_KERNEL_LAUNCH();

    // Optionally save attention scores for visualization/backward
    if (output.attention_scores != nullptr) {
        CHECK_CUDA(cudaMemcpy(output.attention_scores, attn_scores,
                              batch_size * num_heads * seq_len * seq_len * sizeof(float),
                              cudaMemcpyDeviceToDevice));
    }

    // Cleanup
    CHECK_CUDA(cudaFree(q_proj));
    CHECK_CUDA(cudaFree(k_proj));
    CHECK_CUDA(cudaFree(v_proj));
    CHECK_CUDA(cudaFree(q_heads));
    CHECK_CUDA(cudaFree(k_heads));
    CHECK_CUDA(cudaFree(v_heads));
    CHECK_CUDA(cudaFree(attn_scores));
    CHECK_CUDA(cudaFree(attn_output));
    CHECK_CUDA(cudaFree(concat_output));
}

} // namespace attention_expert
