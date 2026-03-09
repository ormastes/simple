/**
 * @file attention_cuda.cu
 * @brief Scaled dot-product attention CUDA kernels
 *
 * Implements a Flash-attention-inspired scaled dot-product attention that
 * computes Attention(Q,K,V) = softmax(Q * K^T / sqrt(d_k)) * V.
 * The implementation chains several small kernels: transpose, matmul, scale,
 * optional causal mask, row-wise softmax, and a final matmul.
 */

#include "native_ops.h"
#include <cuda_runtime.h>
#include <cmath>

/// Tile dimension for matmul sub-kernels
constexpr int ATT_TILE = 32;

// ---- Internal kernels ----

/**
 * @brief Tiled matmul (local copy to avoid cross-TU device symbol linkage issues)
 */
__global__ void att_matmul_kernel(float* __restrict__ C,
                                  const float* __restrict__ A,
                                  const float* __restrict__ B,
                                  int M, int N, int K) {
    __shared__ float sA[ATT_TILE][ATT_TILE];
    __shared__ float sB[ATT_TILE][ATT_TILE];

    int row = blockIdx.y * ATT_TILE + threadIdx.y;
    int col = blockIdx.x * ATT_TILE + threadIdx.x;
    float acc = 0.0f;

    for (int t = 0; t < (K + ATT_TILE - 1) / ATT_TILE; ++t) {
        int aCol = t * ATT_TILE + threadIdx.x;
        int bRow = t * ATT_TILE + threadIdx.y;
        sA[threadIdx.y][threadIdx.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;
        sB[threadIdx.y][threadIdx.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;
        __syncthreads();
        #pragma unroll
        for (int i = 0; i < ATT_TILE; ++i) acc += sA[threadIdx.y][i] * sB[i][threadIdx.x];
        __syncthreads();
    }

    if (row < M && col < N) C[row * N + col] = acc;
}

/**
 * @brief Element-wise scale: data[i] *= scale
 */
__global__ void att_scale_kernel(float* __restrict__ data, float scale, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) data[idx] *= scale;
}

/**
 * @brief Causal mask: set upper triangle to -inf
 */
__global__ void att_causal_mask_kernel(float* __restrict__ scores, int seq_len) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    if (row < seq_len && col < seq_len && col > row) {
        scores[row * seq_len + col] = -1e9f;
    }
}

/**
 * @brief Row-wise softmax with numerical stability (subtract row max)
 */
__global__ void att_softmax_kernel(float* __restrict__ output,
                                   const float* __restrict__ input,
                                   int rows, int cols) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;

    const float* in_row = input + row * cols;
    float* out_row = output + row * cols;

    float max_val = in_row[0];
    for (int j = 1; j < cols; ++j) max_val = fmaxf(max_val, in_row[j]);

    float sum = 0.0f;
    for (int j = 0; j < cols; ++j) {
        out_row[j] = expf(in_row[j] - max_val);
        sum += out_row[j];
    }

    float inv = 1.0f / sum;
    for (int j = 0; j < cols; ++j) out_row[j] *= inv;
}

/**
 * @brief Transpose kernel: out[c*rows+r] = in[r*cols+c]
 */
__global__ void att_transpose_kernel(float* __restrict__ out,
                                     const float* __restrict__ in,
                                     int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < rows * cols) {
        int r = idx / cols;
        int c = idx % cols;
        out[c * rows + r] = in[r * cols + c];
    }
}

// ---- Helper launches ----

static void att_launch_matmul(float* C, const float* A, const float* B,
                               int M, int N, int K, cudaStream_t stream) {
    dim3 block(ATT_TILE, ATT_TILE);
    dim3 grid((N + ATT_TILE - 1) / ATT_TILE, (M + ATT_TILE - 1) / ATT_TILE);
    att_matmul_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}

// ---- Public API ----

void native_attention(float* output, const float* Q, const float* K, const float* V,
                      int seq_len, int head_dim, bool causal, cudaStream_t stream) {
    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));
    int threads = 256;

    // Allocate temporaries
    float *K_t = nullptr, *scores = nullptr, *attn_weights = nullptr;
    cudaMalloc(&K_t, sizeof(float) * seq_len * head_dim);
    cudaMalloc(&scores, sizeof(float) * seq_len * seq_len);
    cudaMalloc(&attn_weights, sizeof(float) * seq_len * seq_len);

    // Step 1: Transpose K [seq x dim] -> K_t [dim x seq]
    int n_kt = seq_len * head_dim;
    att_transpose_kernel<<<(n_kt + threads - 1) / threads, threads, 0, stream>>>(
            K_t, K, seq_len, head_dim);

    // Step 2: scores[seq x seq] = Q[seq x dim] * K_t[dim x seq]
    att_launch_matmul(scores, Q, K_t, seq_len, seq_len, head_dim, stream);
    cudaFree(K_t);

    // Step 3: Scale scores
    int n_scores = seq_len * seq_len;
    att_scale_kernel<<<(n_scores + threads - 1) / threads, threads, 0, stream>>>(
            scores, scale, n_scores);

    // Step 4: Optional causal mask
    if (causal) {
        dim3 mblock(16, 16);
        dim3 mgrid((seq_len + 15) / 16, (seq_len + 15) / 16);
        att_causal_mask_kernel<<<mgrid, mblock, 0, stream>>>(scores, seq_len);
    }

    // Step 5: Softmax
    att_softmax_kernel<<<(seq_len + threads - 1) / threads, threads, 0, stream>>>(
            attn_weights, scores, seq_len, seq_len);
    cudaFree(scores);

    // Step 6: output[seq x dim] = attn_weights[seq x seq] * V[seq x dim]
    att_launch_matmul(output, attn_weights, V, seq_len, head_dim, seq_len, stream);
    cudaFree(attn_weights);
}
