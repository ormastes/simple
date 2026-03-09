/**
 * @file 02_tiled.cu
 * @brief Tiled attention with shared memory for the QK^T computation.
 *
 * Improves over the naive approach by using shared memory tiling for the
 * score computation and a more efficient softmax using warp-level reductions.
 * Still materializes the full attention matrix but with better memory access patterns.
 */

#include "attention/02_tiled.h"
#include <cuda_runtime.h>
#include <cmath>
#include <cfloat>

namespace opt78 {

/// @brief Tile size for shared memory in attention
constexpr int ATTN_TILE = 32;

/**
 * @brief Tiled QK^T computation using shared memory.
 *
 * Each thread block computes a ATTN_TILE x ATTN_TILE tile of the attention
 * score matrix, loading Q and K tiles into shared memory.
 *
 * @param[out] scores  [batch x seq_len x seq_len]
 * @param[in]  Q       [batch x seq_len x head_dim]
 * @param[in]  K       [batch x seq_len x head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Head dimension
 * @param[in]  scale   1 / sqrt(head_dim)
 */
__global__ void tiled_scores_kernel(float* __restrict__ scores,
                                     const float* __restrict__ Q,
                                     const float* __restrict__ K,
                                     int seq_len, int head_dim, float scale) {
    __shared__ float Qs[ATTN_TILE][ATTN_TILE];
    __shared__ float Ks[ATTN_TILE][ATTN_TILE];

    int batch_idx = blockIdx.z;
    int row = blockIdx.y * ATTN_TILE + threadIdx.y;
    int col = blockIdx.x * ATTN_TILE + threadIdx.x;

    float dot = 0.0f;

    for (int t = 0; t < (head_dim + ATTN_TILE - 1) / ATTN_TILE; ++t) {
        int d = t * ATTN_TILE + threadIdx.x;
        if (row < seq_len && d < head_dim)
            Qs[threadIdx.y][threadIdx.x] = Q[batch_idx * seq_len * head_dim + row * head_dim + d];
        else
            Qs[threadIdx.y][threadIdx.x] = 0.0f;

        int d2 = t * ATTN_TILE + threadIdx.y;
        if (col < seq_len && d2 < head_dim)
            Ks[threadIdx.y][threadIdx.x] = K[batch_idx * seq_len * head_dim + col * head_dim + d2];
        else
            Ks[threadIdx.y][threadIdx.x] = 0.0f;

        __syncthreads();

        #pragma unroll
        for (int k = 0; k < ATTN_TILE; ++k) {
            dot += Qs[threadIdx.y][k] * Ks[k][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < seq_len && col < seq_len) {
        scores[batch_idx * seq_len * seq_len + row * seq_len + col] = dot * scale;
    }
}

/**
 * @brief Block-level softmax with shared memory reduction.
 *
 * Each thread block handles one or more rows of the score matrix using
 * shared memory for the max and sum reductions.
 *
 * @param[in,out] scores  [batch x seq_len x seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void tiled_softmax_kernel(float* __restrict__ scores, int seq_len) {
    extern __shared__ float smem[];

    int batch_idx = blockIdx.y;
    int row = blockIdx.x;
    int tid = threadIdx.x;

    float* row_ptr = scores + batch_idx * seq_len * seq_len + row * seq_len;

    // Phase 1: Find max (parallel reduction)
    float local_max = -FLT_MAX;
    for (int j = tid; j < seq_len; j += blockDim.x) {
        local_max = fmaxf(local_max, row_ptr[j]);
    }
    smem[tid] = local_max;
    __syncthreads();

    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            smem[tid] = fmaxf(smem[tid], smem[tid + stride]);
        }
        __syncthreads();
    }
    float max_val = smem[0];
    __syncthreads();

    // Phase 2: Compute exp and sum
    float local_sum = 0.0f;
    for (int j = tid; j < seq_len; j += blockDim.x) {
        float val = expf(row_ptr[j] - max_val);
        row_ptr[j] = val;
        local_sum += val;
    }
    smem[tid] = local_sum;
    __syncthreads();

    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            smem[tid] += smem[tid + stride];
        }
        __syncthreads();
    }
    float total_sum = smem[0];
    __syncthreads();

    // Phase 3: Normalize
    float inv_sum = 1.0f / total_sum;
    for (int j = tid; j < seq_len; j += blockDim.x) {
        row_ptr[j] *= inv_sum;
    }
}

/**
 * @brief Tiled attention * V using shared memory.
 *
 * @param[out] output  [batch x seq_len x head_dim]
 * @param[in]  weights [batch x seq_len x seq_len]
 * @param[in]  V       [batch x seq_len x head_dim]
 * @param[in]  seq_len Sequence length
 * @param[in]  head_dim Head dimension
 */
__global__ void tiled_attn_value_kernel(float* __restrict__ output,
                                         const float* __restrict__ weights,
                                         const float* __restrict__ V,
                                         int seq_len, int head_dim) {
    __shared__ float Ws[ATTN_TILE][ATTN_TILE];
    __shared__ float Vs[ATTN_TILE][ATTN_TILE];

    int batch_idx = blockIdx.z;
    int row = blockIdx.y * ATTN_TILE + threadIdx.y;
    int col = blockIdx.x * ATTN_TILE + threadIdx.x;

    float sum = 0.0f;

    for (int t = 0; t < (seq_len + ATTN_TILE - 1) / ATTN_TILE; ++t) {
        int k_col = t * ATTN_TILE + threadIdx.x;
        if (row < seq_len && k_col < seq_len)
            Ws[threadIdx.y][threadIdx.x] = weights[batch_idx * seq_len * seq_len + row * seq_len + k_col];
        else
            Ws[threadIdx.y][threadIdx.x] = 0.0f;

        int k_row = t * ATTN_TILE + threadIdx.y;
        if (k_row < seq_len && col < head_dim)
            Vs[threadIdx.y][threadIdx.x] = V[batch_idx * seq_len * head_dim + k_row * head_dim + col];
        else
            Vs[threadIdx.y][threadIdx.x] = 0.0f;

        __syncthreads();

        #pragma unroll
        for (int k = 0; k < ATTN_TILE; ++k) {
            sum += Ws[threadIdx.y][k] * Vs[k][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < seq_len && col < head_dim) {
        output[batch_idx * seq_len * head_dim + row * head_dim + col] = sum;
    }
}

void attention_tiled(float* output, float* scores_buf,
                     const float* Q, const float* K, const float* V,
                     int batch, int seq_len, int head_dim,
                     cudaStream_t s) {
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));

    dim3 block(ATTN_TILE, ATTN_TILE);

    // Step 1: Tiled QK^T
    {
        dim3 grid((seq_len + ATTN_TILE - 1) / ATTN_TILE,
                  (seq_len + ATTN_TILE - 1) / ATTN_TILE,
                  batch);
        tiled_scores_kernel<<<grid, block, 0, s>>>(scores_buf, Q, K, seq_len, head_dim, scale);
    }

    // Step 2: Parallel softmax
    {
        int smem_threads = 256;
        dim3 grid_sm(seq_len, batch);
        tiled_softmax_kernel<<<grid_sm, smem_threads, smem_threads * sizeof(float), s>>>(
            scores_buf, seq_len);
    }

    // Step 3: Tiled attention * V
    {
        dim3 grid((head_dim + ATTN_TILE - 1) / ATTN_TILE,
                  (seq_len + ATTN_TILE - 1) / ATTN_TILE,
                  batch);
        tiled_attn_value_kernel<<<grid, block, 0, s>>>(output, scores_buf, V, seq_len, head_dim);
    }
}

}  // namespace opt78
