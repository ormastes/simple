/**
 * @file 03_flash_v2.cu
 * @brief FlashAttention v2 style: online softmax, no materialization of NxN matrix.
 *
 * Implements the FlashAttention algorithm that computes exact attention without
 * materializing the full NxN score matrix. Uses online softmax (tracking running
 * max and sum) and processes K/V in tiles, achieving O(N) memory instead of O(N^2).
 * This enables much longer sequence lengths and better GPU utilization through
 * reduced HBM traffic.
 */

#include "attention/03_flash_v2.h"
#include <cuda_runtime.h>
#include <cmath>
#include <cfloat>

namespace opt78 {

/// @brief Block size for Q tiles (rows processed per block)
constexpr int Br = 32;
/// @brief Block size for K/V tiles (columns processed per iteration)
constexpr int Bc = 32;

/**
 * @brief FlashAttention v2 kernel with online softmax.
 *
 * Each thread block processes Br rows of Q. It iterates over K/V in tiles of
 * size Bc, maintaining running statistics (max and sum) for numerically stable
 * online softmax. The output is accumulated without ever materializing the full
 * attention matrix.
 *
 * Algorithm:
 *  1. For each Q-tile (Br rows):
 *     - Initialize running max m = -inf, running sum l = 0, output O = 0
 *     - For each K/V-tile (Bc columns):
 *       a. Compute S = Q_tile * K_tile^T / sqrt(d)
 *       b. Update m_new = max(m, row_max(S))
 *       c. Rescale: l = l * exp(m - m_new), O = O * exp(m - m_new)
 *       d. P = exp(S - m_new)
 *       e. l += row_sum(P)
 *       f. O += P * V_tile
 *     - Final: O = O / l
 *
 * @param[out] output  [batch x seq_len x head_dim]
 * @param[in]  Q       [batch x seq_len x head_dim]
 * @param[in]  K       [batch x seq_len x head_dim]
 * @param[in]  V       [batch x seq_len x head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Head dimension
 * @param[in]  scale   1 / sqrt(head_dim)
 */
__global__ void flash_attention_v2_kernel(float* __restrict__ output,
                                           const float* __restrict__ Q,
                                           const float* __restrict__ K,
                                           const float* __restrict__ V,
                                           int seq_len, int head_dim, float scale) {
    // Shared memory for K and V tiles
    extern __shared__ float smem[];
    float* Kj = smem;                     // [Bc x head_dim]
    float* Vj = smem + Bc * head_dim;     // [Bc x head_dim]

    int batch_idx = blockIdx.z;
    int q_start = blockIdx.x * Br;

    int tid = threadIdx.x;
    int q_row = q_start + tid;

    // Each thread handles one Q row
    if (tid >= Br) return;

    // Running statistics for online softmax
    float m_i = -FLT_MAX;  // Running max
    float l_i = 0.0f;       // Running sum

    // Output accumulator in registers (one per head_dim element)
    // For large head_dim, we process in chunks
    constexpr int MAX_HD = 128;
    float o_i[MAX_HD] = {};

    int hd = min(head_dim, MAX_HD);

    // Load Q row into registers
    float q_reg[MAX_HD];
    if (q_row < seq_len) {
        for (int d = 0; d < hd; ++d) {
            q_reg[d] = Q[batch_idx * seq_len * head_dim + q_row * head_dim + d];
        }
    }

    // Iterate over K/V tiles
    for (int j = 0; j < seq_len; j += Bc) {
        // Cooperatively load K tile into shared memory
        __syncthreads();
        for (int load = tid; load < Bc * hd; load += Br) {
            int kk = load / hd;
            int dd = load % hd;
            int k_idx = j + kk;
            if (k_idx < seq_len) {
                Kj[kk * hd + dd] = K[batch_idx * seq_len * head_dim + k_idx * head_dim + dd];
                Vj[kk * hd + dd] = V[batch_idx * seq_len * head_dim + k_idx * head_dim + dd];
            } else {
                Kj[kk * hd + dd] = 0.0f;
                Vj[kk * hd + dd] = 0.0f;
            }
        }
        __syncthreads();

        if (q_row >= seq_len) continue;

        // Compute attention scores for this tile: s_ij = q_i * k_j^T * scale
        float tile_max = -FLT_MAX;
        float s_vals[Bc];

        for (int kk = 0; kk < Bc && (j + kk) < seq_len; ++kk) {
            float dot = 0.0f;
            for (int d = 0; d < hd; ++d) {
                dot += q_reg[d] * Kj[kk * hd + d];
            }
            s_vals[kk] = dot * scale;
            tile_max = fmaxf(tile_max, s_vals[kk]);
        }

        // Online softmax update
        float m_new = fmaxf(m_i, tile_max);
        float correction = expf(m_i - m_new);

        // Rescale existing accumulator
        l_i *= correction;
        for (int d = 0; d < hd; ++d) {
            o_i[d] *= correction;
        }

        // Accumulate new tile
        float tile_sum = 0.0f;
        for (int kk = 0; kk < Bc && (j + kk) < seq_len; ++kk) {
            float p = expf(s_vals[kk] - m_new);
            tile_sum += p;

            for (int d = 0; d < hd; ++d) {
                o_i[d] += p * Vj[kk * hd + d];
            }
        }

        m_i = m_new;
        l_i += tile_sum;
    }

    // Final normalization
    if (q_row < seq_len && l_i > 0.0f) {
        float inv_l = 1.0f / l_i;
        for (int d = 0; d < hd; ++d) {
            output[batch_idx * seq_len * head_dim + q_row * head_dim + d] = o_i[d] * inv_l;
        }
    }
}

void attention_flash_v2(float* output,
                        const float* Q, const float* K, const float* V,
                        int batch, int seq_len, int head_dim,
                        cudaStream_t s) {
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));

    int hd = head_dim < 128 ? head_dim : 128;
    size_t smem_size = 2 * Bc * hd * sizeof(float);

    dim3 block(Br);
    dim3 grid((seq_len + Br - 1) / Br, 1, batch);

    flash_attention_v2_kernel<<<grid, block, smem_size, s>>>(
        output, Q, K, V, seq_len, head_dim, scale);
}

}  // namespace opt78
