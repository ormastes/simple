/**
 * @file flash_attention.cu
 * @brief Tiled Scaled Dot-Product Attention (FlashAttention-style)
 *
 * Implements a simplified FlashAttention-style tiled SDPA kernel. Instead of
 * materializing the full N x N attention matrix, the kernel processes key/value
 * tiles incrementally using online softmax to maintain numerical stability.
 * This approach reduces peak memory from O(N^2) to O(N * tile_size).
 */
#include <cuda_runtime.h>
#include <cfloat>
#include <cmath>

namespace transformer {

#define FA_TILE_SIZE 32

/**
 * @brief Simple (non-fused) scaled dot-product attention with tiled processing
 *
 * Each CUDA block processes one query position. The kernel iterates over key tiles,
 * computes QK^T scores for the tile, applies online softmax to maintain a running
 * maximum and sum of exponentials, and accumulates the weighted value vectors (PV).
 *
 * @param[out] output   Attention output [seq_len, head_dim]
 * @param[in]  Q        Query matrix [seq_len, head_dim]
 * @param[in]  K        Key matrix [seq_len, head_dim]
 * @param[in]  V        Value matrix [seq_len, head_dim]
 * @param[in]  seq_len  Sequence length
 * @param[in]  head_dim Head dimension
 * @param[in]  scale    Scaling factor (1 / sqrt(head_dim))
 * @param[in]  causal   Whether to apply causal masking
 */
__global__ void sdpa_tiled_kernel(float* __restrict__ output,
                                   const float* __restrict__ Q,
                                   const float* __restrict__ K,
                                   const float* __restrict__ V,
                                   int seq_len, int head_dim, float scale,
                                   bool causal) {
    int q_idx = blockIdx.x;  // One block per query position
    if (q_idx >= seq_len) return;

    extern __shared__ float smem[];
    float* scores = smem;  // [FA_TILE_SIZE]

    // Initialize output accumulator and softmax state
    float max_val = -FLT_MAX;
    float sum_exp = 0.0f;

    // Per-thread output accumulator (max supported head_dim = 128)
    float out_acc[128];
    for (int d = 0; d < head_dim; d++) {
        out_acc[d] = 0.0f;
    }

    // Determine the upper bound for key iteration
    int max_k = causal ? (q_idx + 1) : seq_len;

    // Iterate over key tiles
    for (int k_start = 0; k_start < max_k; k_start += FA_TILE_SIZE) {
        int k_end = min(k_start + FA_TILE_SIZE, max_k);

        // Compute QK^T scores for this tile
        for (int ki = k_start + threadIdx.x; ki < k_end; ki += blockDim.x) {
            float score = 0.0f;
            for (int d = 0; d < head_dim; d++) {
                score += Q[q_idx * head_dim + d] * K[ki * head_dim + d];
            }
            scores[ki - k_start] = score * scale;
        }
        __syncthreads();

        // Online softmax update and PV accumulation (single thread for simplicity)
        if (threadIdx.x == 0) {
            for (int ki = 0; ki < (k_end - k_start); ki++) {
                float new_max = fmaxf(max_val, scores[ki]);
                float exp_diff = expf(max_val - new_max);

                // Rescale previous accumulators to account for new maximum
                for (int d = 0; d < head_dim; d++) {
                    out_acc[d] *= exp_diff;
                }
                sum_exp = sum_exp * exp_diff;

                float p = expf(scores[ki] - new_max);
                sum_exp += p;
                max_val = new_max;

                // Accumulate weighted value vector
                int k_global = k_start + ki;
                for (int d = 0; d < head_dim; d++) {
                    out_acc[d] += p * V[k_global * head_dim + d];
                }
            }
        }
        __syncthreads();
    }

    // Write normalized output
    if (threadIdx.x == 0) {
        float inv_sum = 1.0f / sum_exp;
        for (int d = 0; d < head_dim; d++) {
            output[q_idx * head_dim + d] = out_acc[d] * inv_sum;
        }
    }
}

/**
 * @brief Launch tiled scaled dot-product attention
 *
 * Launches one kernel per (batch, head) pair. Each kernel processes all query
 * positions for that batch element and attention head.
 *
 * @param[out] output    Output tensor [batch, num_heads, seq_len, head_dim]
 * @param[in]  Q         Query tensor [batch, num_heads, seq_len, head_dim]
 * @param[in]  K         Key tensor [batch, num_heads, seq_len, head_dim]
 * @param[in]  V         Value tensor [batch, num_heads, seq_len, head_dim]
 * @param[in]  batch     Batch size
 * @param[in]  num_heads Number of attention heads
 * @param[in]  seq_len   Sequence length
 * @param[in]  head_dim  Head dimension (max 128)
 * @param[in]  causal    Whether to apply causal masking
 * @param[in]  stream    CUDA stream
 */
void launch_flash_attention(float* output, const float* Q, const float* K, const float* V,
                            int batch, int num_heads, int seq_len, int head_dim,
                            bool causal, cudaStream_t stream) {
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));
    int smem_size = FA_TILE_SIZE * sizeof(float);

    // Launch per batch per head
    for (int b = 0; b < batch; b++) {
        for (int h = 0; h < num_heads; h++) {
            int offset = (b * num_heads + h) * seq_len * head_dim;
            sdpa_tiled_kernel<<<seq_len, 32, smem_size, stream>>>(
                output + offset, Q + offset, K + offset, V + offset,
                seq_len, head_dim, scale, causal);
        }
    }
}

#undef FA_TILE_SIZE

} // namespace transformer
