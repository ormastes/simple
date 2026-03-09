/**
 * @file multi_head_attention.cu
 * @brief CUDA implementation of multi-head attention
 *
 * Implements the complete multi-head attention mechanism:
 * 1. Linear projections: input -> Q, K, V via weight matrices
 * 2. Per-head scaled dot-product attention (with optional causal mask)
 * 3. Concatenation of heads and output projection
 *
 * This is a naive reference implementation using simple matrix multiply
 * kernels. Production code would use cuBLAS or fused attention kernels.
 */

#include "common/multi_head_attention.h"
#include "common/causal_attention.h"
#include "cuda_utils.h"
#include <cmath>

namespace llm {

/**
 * @brief Naive matrix multiply + bias: C = A * B^T + bias
 *
 * Computes output[i][j] = sum_k input[i][k] * weight[j][k] + bias[j]
 * where weight is stored as [out_dim, in_dim] (row-major).
 *
 * @param[out] output  Output matrix [rows, out_dim]
 * @param[in]  input   Input matrix [rows, in_dim]
 * @param[in]  weight  Weight matrix [out_dim, in_dim]
 * @param[in]  bias    Bias vector [out_dim]
 * @param[in]  rows    Number of rows
 * @param[in]  in_dim  Input dimension
 * @param[in]  out_dim Output dimension
 */
__global__ void linear_forward_kernel(
    float* output,
    const float* input,
    const float* weight,
    const float* bias,
    int rows,
    int in_dim,
    int out_dim
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < rows && col < out_dim) {
        float sum = 0.0f;
        for (int k = 0; k < in_dim; ++k) {
            sum += input[row * in_dim + k] * weight[col * in_dim + k];
        }
        sum += bias[col];
        output[row * out_dim + col] = sum;
    }
}

/**
 * @brief Launch linear projection kernel
 *
 * @param output [rows, out_dim]
 * @param input  [rows, in_dim]
 * @param weight [out_dim, in_dim]
 * @param bias   [out_dim]
 * @param rows   Number of rows (batch_size * seq_len)
 * @param in_dim Input dimension
 * @param out_dim Output dimension
 * @param stream CUDA stream
 */
static void linear_forward(float* output, const float* input,
                           const float* weight, const float* bias,
                           int rows, int in_dim, int out_dim,
                           cudaStream_t stream) {
    dim3 block(16, 16);
    dim3 grid((rows + 15) / 16, (out_dim + 15) / 16);

    linear_forward_kernel<<<grid, block, 0, stream>>>(
        output, input, weight, bias, rows, in_dim, out_dim);
}

void multi_head_attention_forward(float* output, const float* input,
                                 const AttentionWeights& weights,
                                 const AttentionConfig& config,
                                 int batch_size, int seq_len,
                                 bool causal,
                                 cudaStream_t stream) {
    int d_model = config.d_model;
    int total_tokens = batch_size * seq_len;

    // Allocate intermediate buffers for Q, K, V projections
    // Each is [batch_size * seq_len, d_model]
    float* d_Q = nullptr;
    float* d_K = nullptr;
    float* d_V = nullptr;
    float* d_attn_out = nullptr;

    size_t proj_bytes = total_tokens * d_model * sizeof(float);
    CHECK_CUDA(cudaMalloc(&d_Q, proj_bytes));
    CHECK_CUDA(cudaMalloc(&d_K, proj_bytes));
    CHECK_CUDA(cudaMalloc(&d_V, proj_bytes));
    CHECK_CUDA(cudaMalloc(&d_attn_out, proj_bytes));

    // Step 1: Project input to Q, K, V
    // Q = input * W_Q^T + b_Q
    linear_forward(d_Q, input, weights.W_Q, weights.b_Q,
                   total_tokens, d_model, d_model, stream);
    // K = input * W_K^T + b_K
    linear_forward(d_K, input, weights.W_K, weights.b_K,
                   total_tokens, d_model, d_model, stream);
    // V = input * W_V^T + b_V
    linear_forward(d_V, input, weights.W_V, weights.b_V,
                   total_tokens, d_model, d_model, stream);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    // Step 2-3: Compute attention (splits into heads internally)
    if (causal) {
        causal_attention_forward(d_attn_out, d_Q, d_K, d_V,
                                config, batch_size, seq_len, stream);
    } else {
        self_attention_forward(d_attn_out, d_Q, d_K, d_V,
                              config, batch_size, seq_len, stream);
    }

    // Step 4: Output projection: output = attn_out * W_O^T + b_O
    linear_forward(output, d_attn_out, weights.W_O, weights.b_O,
                   total_tokens, d_model, d_model, stream);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    // Clean up
    cudaFree(d_Q);
    cudaFree(d_K);
    cudaFree(d_V);
    cudaFree(d_attn_out);
}

} // namespace llm
