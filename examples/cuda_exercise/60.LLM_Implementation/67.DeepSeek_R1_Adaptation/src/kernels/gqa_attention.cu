/**
 * @file gqa_attention.cu
 * @brief CUDA implementation of Grouped Query Attention
 *
 * Implements GQA where each KV head is shared among multiple query heads.
 * The query heads are split into groups of (num_heads / num_kv_heads), and
 * all heads within a group attend to the same key/value pair. This reduces
 * KV cache memory by a factor of (num_heads / num_kv_heads) compared to MHA.
 */

#include "common/gqa_attention.h"
#include "cuda_utils.h"
#include <cmath>
#include <cfloat>

namespace llm {

/**
 * @brief Naive linear projection kernel: Y = X * W^T + b
 *
 * Computes matrix multiplication for projecting input through weight matrices.
 * Each thread computes one element of the output.
 *
 * @param[out] Y       Output [total_tokens, out_dim]
 * @param[in]  X       Input [total_tokens, in_dim]
 * @param[in]  W       Weight [out_dim, in_dim] (stored row-major, applied as X * W^T)
 * @param[in]  bias    Bias [out_dim] (may be nullptr)
 * @param[in]  total_tokens  batch_size * seq_len
 * @param[in]  in_dim  Input dimension
 * @param[in]  out_dim Output dimension
 */
__global__ void linear_project_kernel(
    float* Y, const float* X, const float* W, const float* bias,
    int total_tokens, int in_dim, int out_dim
) {
    int token = blockIdx.x * blockDim.x + threadIdx.x;
    int od = blockIdx.y * blockDim.y + threadIdx.y;

    if (token < total_tokens && od < out_dim) {
        float sum = 0.0f;
        for (int k = 0; k < in_dim; ++k) {
            sum += X[token * in_dim + k] * W[od * in_dim + k];
        }
        if (bias) sum += bias[od];
        Y[token * out_dim + od] = sum;
    }
}

/**
 * @brief GQA attention scores kernel with group-shared KV
 *
 * Computes attention scores for one batch element, one query head.
 * The KV head index is derived as (query_head / group_size).
 *
 * @param[out] scores    Output [seq_len, seq_len]
 * @param[in]  Q_head    Query for one head [seq_len, head_dim]
 * @param[in]  K_head    Key for the shared KV head [seq_len, head_dim]
 * @param[in]  seq_len   Sequence length
 * @param[in]  head_dim  Dimension per head
 * @param[in]  scale     Scaling factor (1/sqrt(head_dim))
 * @param[in]  causal    Whether to apply causal masking
 */
__global__ void gqa_scores_kernel(
    float* scores,
    const float* Q_head,
    const float* K_head,
    int seq_len,
    int head_dim,
    float scale,
    bool causal
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < seq_len && col < seq_len) {
        if (causal && col > row) {
            scores[row * seq_len + col] = -FLT_MAX;
            return;
        }
        float dot = 0.0f;
        for (int k = 0; k < head_dim; ++k) {
            dot += Q_head[row * head_dim + k] * K_head[col * head_dim + k];
        }
        scores[row * seq_len + col] = dot * scale;
    }
}

/**
 * @brief Row-wise softmax kernel
 *
 * Applies numerically stable softmax to each row independently.
 *
 * @param[in,out] scores Attention scores [seq_len, seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void gqa_softmax_kernel(float* scores, int seq_len) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < seq_len) {
        float max_val = -FLT_MAX;
        for (int j = 0; j < seq_len; ++j) {
            float v = scores[row * seq_len + j];
            if (v > max_val) max_val = v;
        }

        float sum = 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            float e = expf(scores[row * seq_len + j] - max_val);
            scores[row * seq_len + j] = e;
            sum += e;
        }

        float inv = (sum > 0.0f) ? (1.0f / sum) : 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            scores[row * seq_len + j] *= inv;
        }
    }
}

/**
 * @brief Attention-value multiplication: out = attn * V
 *
 * @param[out] output      [seq_len, head_dim]
 * @param[in]  attn        Attention weights [seq_len, seq_len]
 * @param[in]  V_head      Value tensor [seq_len, head_dim]
 * @param[in]  seq_len     Sequence length
 * @param[in]  head_dim    Dimension per head
 */
__global__ void gqa_attn_value_kernel(
    float* output, const float* attn, const float* V_head,
    int seq_len, int head_dim
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int dim = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < seq_len && dim < head_dim) {
        float sum = 0.0f;
        for (int j = 0; j < seq_len; ++j) {
            sum += attn[row * seq_len + j] * V_head[j * head_dim + dim];
        }
        output[row * head_dim + dim] = sum;
    }
}

void gqa_forward(float* output, const float* input,
                 const GQAWeights& weights,
                 const DeepSeekConfig& config,
                 int batch_size, int seq_len,
                 bool causal,
                 cudaStream_t stream) {
    int d_model = config.d_model;
    int num_heads = config.num_heads;
    int num_kv_heads = config.num_kv_heads;
    int head_dim = d_model / num_heads;
    int group_size = num_heads / num_kv_heads;
    int total_tokens = batch_size * seq_len;
    int q_dim = num_heads * head_dim;
    int kv_dim = num_kv_heads * head_dim;
    float scale = 1.0f / std::sqrt(static_cast<float>(head_dim));

    // Allocate projected Q, K, V
    float *d_Q = nullptr, *d_K = nullptr, *d_V = nullptr;
    CHECK_CUDA(cudaMalloc(&d_Q, total_tokens * q_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_K, total_tokens * kv_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_V, total_tokens * kv_dim * sizeof(float)));

    // Project input -> Q, K, V
    dim3 proj_block(16, 16);
    dim3 proj_grid_q((total_tokens + 15) / 16, (q_dim + 15) / 16);
    dim3 proj_grid_kv((total_tokens + 15) / 16, (kv_dim + 15) / 16);

    linear_project_kernel<<<proj_grid_q, proj_block, 0, stream>>>(
        d_Q, input, weights.W_Q, weights.b_Q, total_tokens, d_model, q_dim);
    linear_project_kernel<<<proj_grid_kv, proj_block, 0, stream>>>(
        d_K, input, weights.W_K, weights.b_K, total_tokens, d_model, kv_dim);
    linear_project_kernel<<<proj_grid_kv, proj_block, 0, stream>>>(
        d_V, input, weights.W_V, weights.b_V, total_tokens, d_model, kv_dim);

    // Allocate temporary buffers for per-head attention
    float *d_scores = nullptr, *d_out_head = nullptr;
    CHECK_CUDA(cudaMalloc(&d_scores, seq_len * seq_len * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out_head, seq_len * head_dim * sizeof(float)));

    // Allocate concatenated output before W_O projection
    float* d_concat = nullptr;
    CHECK_CUDA(cudaMalloc(&d_concat, total_tokens * q_dim * sizeof(float)));

    dim3 score_block(16, 16);
    dim3 score_grid((seq_len + 15) / 16, (seq_len + 15) / 16);
    dim3 val_block(16, 16);
    dim3 val_grid((seq_len + 15) / 16, (head_dim + 15) / 16);
    int sm_threads = 256;
    int sm_blocks = (seq_len + sm_threads - 1) / sm_threads;

    for (int b = 0; b < batch_size; ++b) {
        for (int h = 0; h < num_heads; ++h) {
            int kv_h = h / group_size;  // Which KV head this query head shares

            // Q head pointer: d_Q[b * seq_len * q_dim + s * q_dim + h * head_dim]
            // K head pointer: d_K[b * seq_len * kv_dim + s * kv_dim + kv_h * head_dim]
            const float* q_base = d_Q + b * seq_len * q_dim;
            const float* k_base = d_K + b * seq_len * kv_dim;
            const float* v_base = d_V + b * seq_len * kv_dim;

            // We need contiguous per-head slices; extract them via strided copy
            // For simplicity, use cudaMemcpy2D to extract head_dim columns at the right offset
            CHECK_CUDA(cudaMemcpy2DAsync(
                d_out_head, head_dim * sizeof(float),          // dst, dpitch
                q_base + h * head_dim, q_dim * sizeof(float),  // src, spitch
                head_dim * sizeof(float), seq_len,              // width, height
                cudaMemcpyDeviceToDevice, stream));

            float* d_q_head_tmp = d_out_head;  // reuse buffer temporarily

            // Actually we need separate buffers for Q, K, V heads simultaneously
            // Allocate small per-head buffers
            float *d_q_h = nullptr, *d_k_h = nullptr, *d_v_h = nullptr;
            CHECK_CUDA(cudaMalloc(&d_q_h, seq_len * head_dim * sizeof(float)));
            CHECK_CUDA(cudaMalloc(&d_k_h, seq_len * head_dim * sizeof(float)));
            CHECK_CUDA(cudaMalloc(&d_v_h, seq_len * head_dim * sizeof(float)));

            // Extract Q head h
            CHECK_CUDA(cudaMemcpy2DAsync(
                d_q_h, head_dim * sizeof(float),
                q_base + h * head_dim, q_dim * sizeof(float),
                head_dim * sizeof(float), seq_len,
                cudaMemcpyDeviceToDevice, stream));

            // Extract K head kv_h
            CHECK_CUDA(cudaMemcpy2DAsync(
                d_k_h, head_dim * sizeof(float),
                k_base + kv_h * head_dim, kv_dim * sizeof(float),
                head_dim * sizeof(float), seq_len,
                cudaMemcpyDeviceToDevice, stream));

            // Extract V head kv_h
            CHECK_CUDA(cudaMemcpy2DAsync(
                d_v_h, head_dim * sizeof(float),
                v_base + kv_h * head_dim, kv_dim * sizeof(float),
                head_dim * sizeof(float), seq_len,
                cudaMemcpyDeviceToDevice, stream));

            // Compute attention scores
            gqa_scores_kernel<<<score_grid, score_block, 0, stream>>>(
                d_scores, d_q_h, d_k_h, seq_len, head_dim, scale, causal);

            // Softmax
            gqa_softmax_kernel<<<sm_blocks, sm_threads, 0, stream>>>(
                d_scores, seq_len);

            // Multiply by V
            gqa_attn_value_kernel<<<val_grid, val_block, 0, stream>>>(
                d_out_head, d_scores, d_v_h, seq_len, head_dim);

            // Scatter output head h into concatenated buffer
            CHECK_CUDA(cudaMemcpy2DAsync(
                d_concat + b * seq_len * q_dim + h * head_dim, q_dim * sizeof(float),
                d_out_head, head_dim * sizeof(float),
                head_dim * sizeof(float), seq_len,
                cudaMemcpyDeviceToDevice, stream));

            cudaFree(d_q_h);
            cudaFree(d_k_h);
            cudaFree(d_v_h);
        }
    }

    // Output projection: output = concat * W_O^T + b_O
    dim3 out_grid((total_tokens + 15) / 16, (d_model + 15) / 16);
    linear_project_kernel<<<out_grid, proj_block, 0, stream>>>(
        output, d_concat, weights.W_O, weights.b_O, total_tokens, q_dim, d_model);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    cudaFree(d_Q);
    cudaFree(d_K);
    cudaFree(d_V);
    cudaFree(d_scores);
    cudaFree(d_out_head);
    cudaFree(d_concat);
}

} // namespace llm
