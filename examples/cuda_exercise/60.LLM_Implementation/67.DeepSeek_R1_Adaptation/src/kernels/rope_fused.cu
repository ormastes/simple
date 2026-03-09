/**
 * @file rope_fused.cu
 * @brief Fused CUDA kernel for Rotary Position Embeddings (RoPE)
 *
 * Implements RoPE by applying in-place rotation to pairs of dimensions in
 * Q and K tensors. Supports configurable base theta and NTK-aware scaling
 * for context length extension.
 *
 * Each thread handles one dimension pair (2i, 2i+1) at one position in
 * one head, applying:
 *   x_rot = x[2i]*cos(angle) - x[2i+1]*sin(angle)
 *   y_rot = x[2i]*sin(angle) + x[2i+1]*cos(angle)
 */

#include "common/rope_embeddings.h"
#include "cuda_utils.h"
#include <cmath>

namespace llm {

/**
 * @brief Apply RoPE rotation to a single tensor in-place
 *
 * Each thread handles one (token, head, dim_pair) combination. The frequency
 * is computed as: freq = 1.0 / (theta^(2*dim_pair / head_dim))
 * and the rotation angle is: angle = position * freq
 *
 * @param[in,out] tensor     Input/output [batch, seq_len, num_heads * head_dim]
 * @param[in]     seq_len    Sequence length
 * @param[in]     num_heads  Number of heads in this tensor
 * @param[in]     head_dim   Dimension per head (must be even)
 * @param[in]     theta      Base frequency
 * @param[in]     pos_offset Position offset for KV-cache scenarios
 * @param[in]     total_heads_x_halfhead  num_heads * (head_dim / 2) for grid sizing
 */
__global__ void rope_apply_kernel(
    float* tensor,
    int seq_len,
    int num_heads,
    int head_dim,
    float theta,
    int pos_offset,
    int stride // num_heads * head_dim
) {
    // Global thread index maps to (batch_token, head_pair)
    int batch_token = blockIdx.x * blockDim.x + threadIdx.x;
    int head_pair = blockIdx.y * blockDim.y + threadIdx.y;

    int total_tokens = gridDim.x * blockDim.x;  // approximate
    int half_head = head_dim / 2;
    int total_pairs = num_heads * half_head;

    if (head_pair >= total_pairs) return;
    if (batch_token >= total_tokens) return;

    int h = head_pair / half_head;
    int d = head_pair % half_head;

    int pos = batch_token % seq_len + pos_offset;
    int batch_idx = batch_token / seq_len;

    // Compute frequency: 1.0 / (theta ^ (2*d / head_dim))
    float freq = 1.0f / powf(theta, (2.0f * d) / static_cast<float>(head_dim));
    float angle = static_cast<float>(pos) * freq;
    float cos_val = cosf(angle);
    float sin_val = sinf(angle);

    // Index into the flat tensor [batch, seq_len, num_heads * head_dim]
    int base = batch_idx * seq_len * stride + (batch_token % seq_len) * stride + h * head_dim;
    int idx0 = base + 2 * d;
    int idx1 = base + 2 * d + 1;

    float x0 = tensor[idx0];
    float x1 = tensor[idx1];

    tensor[idx0] = x0 * cos_val - x1 * sin_val;
    tensor[idx1] = x0 * sin_val + x1 * cos_val;
}

void rope_forward(float* Q, float* K,
                  const RoPEConfig& config,
                  int batch_size, int seq_len,
                  int num_heads, int num_kv_heads,
                  int pos_offset,
                  cudaStream_t stream) {
    int head_dim = config.head_dim;
    int half_head = head_dim / 2;

    // Apply NTK-aware scaling if alpha != 1.0
    float effective_theta = config.theta;
    if (config.ntk_alpha != 1.0f) {
        effective_theta = config.theta * powf(config.ntk_alpha,
                          static_cast<float>(head_dim) / static_cast<float>(head_dim - 2));
    }

    int total_tokens = batch_size * seq_len;

    // Apply RoPE to Q
    {
        int total_pairs = num_heads * half_head;
        dim3 block(16, 16);
        dim3 grid((total_tokens + block.x - 1) / block.x,
                  (total_pairs + block.y - 1) / block.y);
        int stride = num_heads * head_dim;

        rope_apply_kernel<<<grid, block, 0, stream>>>(
            Q, seq_len, num_heads, head_dim,
            effective_theta, pos_offset, stride);
    }

    // Apply RoPE to K
    {
        int total_pairs = num_kv_heads * half_head;
        dim3 block(16, 16);
        dim3 grid((total_tokens + block.x - 1) / block.x,
                  (total_pairs + block.y - 1) / block.y);
        int stride = num_kv_heads * head_dim;

        rope_apply_kernel<<<grid, block, 0, stream>>>(
            K, seq_len, num_kv_heads, head_dim,
            effective_theta, pos_offset, stride);
    }

    CHECK_CUDA(cudaStreamSynchronize(stream));
}

/**
 * @brief Precompute cos/sin frequency table kernel
 *
 * @param[out] cos_table [max_seq_len, half_head]
 * @param[out] sin_table [max_seq_len, half_head]
 * @param[in]  head_dim  Dimension per head
 * @param[in]  theta     Base frequency
 * @param[in]  max_seq_len Maximum sequence length
 */
__global__ void rope_precompute_kernel(
    float* cos_table, float* sin_table,
    int head_dim, float theta, int max_seq_len
) {
    int pos = blockIdx.x * blockDim.x + threadIdx.x;
    int d = blockIdx.y * blockDim.y + threadIdx.y;
    int half_head = head_dim / 2;

    if (pos < max_seq_len && d < half_head) {
        float freq = 1.0f / powf(theta, (2.0f * d) / static_cast<float>(head_dim));
        float angle = static_cast<float>(pos) * freq;
        cos_table[pos * half_head + d] = cosf(angle);
        sin_table[pos * half_head + d] = sinf(angle);
    }
}

void rope_precompute_freqs(float* cos_table, float* sin_table,
                           const RoPEConfig& config,
                           cudaStream_t stream) {
    int half_head = config.head_dim / 2;

    float effective_theta = config.theta;
    if (config.ntk_alpha != 1.0f) {
        effective_theta = config.theta * powf(config.ntk_alpha,
                          static_cast<float>(config.head_dim) /
                          static_cast<float>(config.head_dim - 2));
    }

    dim3 block(16, 16);
    dim3 grid((config.max_seq_len + 15) / 16, (half_head + 15) / 16);

    rope_precompute_kernel<<<grid, block, 0, stream>>>(
        cos_table, sin_table, config.head_dim,
        effective_theta, config.max_seq_len);

    CHECK_CUDA(cudaStreamSynchronize(stream));
}

} // namespace llm
