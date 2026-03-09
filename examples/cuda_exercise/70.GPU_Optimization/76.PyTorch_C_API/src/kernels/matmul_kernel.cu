/**
 * @file matmul_kernel.cu
 * @brief Tiled CUDA matrix multiplication kernel with shared memory
 *
 * Implements a 32x32 tiled matrix multiplication that loads sub-blocks of A and B
 * into shared memory to reduce global memory traffic. This kernel is called by the
 * C API layer (torch_matmul) and serves as the GPU compute backend for the
 * PyTorch ctypes integration path.
 */

#include "matmul_kernel.h"
#include <cuda_runtime.h>

/// Tile dimension for shared-memory blocking
constexpr int TILE_SIZE = 32;

/**
 * @brief Tiled matmul kernel: C[M x N] = A[M x K] * B[K x N]
 *
 * Each thread block computes a TILE_SIZE x TILE_SIZE output tile. The kernel
 * iterates over K in TILE_SIZE steps, loading one tile of A and one tile of B
 * into shared memory per step, synchronising, then accumulating the partial
 * dot products.
 *
 * @param[out] C  Output matrix (row-major, device memory)
 * @param[in]  A  Left input matrix (row-major, device memory)
 * @param[in]  B  Right input matrix (row-major, device memory)
 * @param[in]  M  Number of rows in A / C
 * @param[in]  N  Number of columns in B / C
 * @param[in]  K  Number of columns in A / rows in B
 */
__global__ void tiled_matmul_kernel(float* __restrict__ C,
                                    const float* __restrict__ A,
                                    const float* __restrict__ B,
                                    int M, int N, int K) {
    __shared__ float tileA[TILE_SIZE][TILE_SIZE];
    __shared__ float tileB[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;

    float sum = 0.0f;

    // Iterate over tiles along the K dimension
    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; ++t) {
        int aCol = t * TILE_SIZE + threadIdx.x;
        int bRow = t * TILE_SIZE + threadIdx.y;

        // Load tile of A into shared memory (boundary check)
        if (row < M && aCol < K) {
            tileA[threadIdx.y][threadIdx.x] = A[row * K + aCol];
        } else {
            tileA[threadIdx.y][threadIdx.x] = 0.0f;
        }

        // Load tile of B into shared memory (boundary check)
        if (bRow < K && col < N) {
            tileB[threadIdx.y][threadIdx.x] = B[bRow * N + col];
        } else {
            tileB[threadIdx.y][threadIdx.x] = 0.0f;
        }

        __syncthreads();

        // Accumulate partial dot products from this tile
        #pragma unroll
        for (int i = 0; i < TILE_SIZE; ++i) {
            sum += tileA[threadIdx.y][i] * tileB[i][threadIdx.x];
        }

        __syncthreads();
    }

    // Write result
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

/**
 * @brief Add bias to each row: output[i][j] += bias[j]
 *
 * @param[in,out] output  Matrix [rows x cols]
 * @param[in]     bias    Bias vector [cols]
 * @param[in]     rows    Number of rows
 * @param[in]     cols    Number of columns
 */
__global__ void add_bias_kernel(float* __restrict__ output,
                                const float* __restrict__ bias,
                                int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < rows * cols) {
        int col = idx % cols;
        output[idx] += bias[col];
    }
}

/**
 * @brief Row-wise softmax: out[i][j] = exp(in[i][j]) / sum_j(exp(in[i][j]))
 *
 * Uses the numerically stable trick of subtracting the row maximum before
 * exponentiation.
 *
 * @param[out] output  Softmax result [rows x cols]
 * @param[in]  input   Input matrix   [rows x cols]
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 */
__global__ void softmax_kernel(float* __restrict__ output,
                               const float* __restrict__ input,
                               int rows, int cols) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;

    const float* in_row = input + row * cols;
    float* out_row = output + row * cols;

    // Find row maximum for numerical stability
    float max_val = in_row[0];
    for (int j = 1; j < cols; ++j) {
        max_val = fmaxf(max_val, in_row[j]);
    }

    // Compute exp and sum
    float sum = 0.0f;
    for (int j = 0; j < cols; ++j) {
        out_row[j] = expf(in_row[j] - max_val);
        sum += out_row[j];
    }

    // Normalize
    float inv_sum = 1.0f / sum;
    for (int j = 0; j < cols; ++j) {
        out_row[j] *= inv_sum;
    }
}

/**
 * @brief Apply lower-triangular causal mask (set upper triangle to -inf)
 *
 * @param[in,out] scores  Attention score matrix [seq_len x seq_len]
 * @param[in]     seq_len Sequence length
 */
__global__ void causal_mask_kernel(float* __restrict__ scores, int seq_len) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    if (row < seq_len && col < seq_len && col > row) {
        scores[row * seq_len + col] = -1e9f;
    }
}

/**
 * @brief Reduce rows to compute column sums: out[j] = sum_i(input[i][j])
 *
 * Simple single-block-per-column reduction used for grad_bias computation.
 *
 * @param[out] output  Column sums [cols]
 * @param[in]  input   Input matrix [rows x cols]
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 */
__global__ void reduce_rows_kernel(float* __restrict__ output,
                                   const float* __restrict__ input,
                                   int rows, int cols) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    if (col >= cols) return;

    float sum = 0.0f;
    for (int i = 0; i < rows; ++i) {
        sum += input[i * cols + col];
    }
    output[col] = sum;
}

// ---- Host-callable wrappers ----

void launch_tiled_matmul(float* C, const float* A, const float* B,
                         int M, int N, int K, cudaStream_t stream) {
    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);
    tiled_matmul_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}

void launch_add_bias(float* output, const float* bias, int rows, int cols,
                     cudaStream_t stream) {
    int total = rows * cols;
    int threads = 256;
    int blocks = (total + threads - 1) / threads;
    add_bias_kernel<<<blocks, threads, 0, stream>>>(output, bias, rows, cols);
}

void launch_softmax(float* output, const float* input, int rows, int cols,
                    cudaStream_t stream) {
    int threads = 256;
    int blocks = (rows + threads - 1) / threads;
    softmax_kernel<<<blocks, threads, 0, stream>>>(output, input, rows, cols);
}

void launch_causal_mask(float* scores, int seq_len, cudaStream_t stream) {
    dim3 block(16, 16);
    dim3 grid((seq_len + 15) / 16, (seq_len + 15) / 16);
    causal_mask_kernel<<<grid, block, 0, stream>>>(scores, seq_len);
}

void launch_reduce_rows(float* output, const float* input, int rows, int cols,
                        cudaStream_t stream) {
    int threads = 256;
    int blocks = (cols + threads - 1) / threads;
    reduce_rows_kernel<<<blocks, threads, 0, stream>>>(output, input, rows, cols);
}

/**
 * @brief Element-wise scale kernel: data[i] *= scale
 */
__global__ void scale_kernel(float* __restrict__ data, float scale, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] *= scale;
    }
}

void launch_scale(float* data, float scale, int n, cudaStream_t stream) {
    int threads = 256;
    int blocks = (n + threads - 1) / threads;
    scale_kernel<<<blocks, threads, 0, stream>>>(data, scale, n);
}
