/**
 * @file 02_shared_memory.cu
 * @brief Shared memory tiled matrix multiplication with 16x16 tiles.
 *
 * Loads tiles of A and B into shared memory before computing partial sums.
 * This reduces global memory accesses by a factor of TILE_SIZE, improving
 * performance to around 200 GFLOPS through better data reuse.
 */

#include "matmul/02_shared_memory.h"
#include <cuda_runtime.h>

namespace opt78 {

/// @brief Tile dimension for shared memory blocking
constexpr int SMEM_TILE = 16;

/**
 * @brief Shared memory tiled matmul kernel.
 *
 * Each thread block loads TILE x TILE sub-matrices of A and B into shared
 * memory, computes partial products, and accumulates across K-dimension tiles.
 *
 * @param[out] C Output matrix [M x N]
 * @param[in]  A Input matrix [M x K]
 * @param[in]  B Input matrix [K x N]
 * @param[in]  M Rows of A
 * @param[in]  N Cols of B
 * @param[in]  K Inner dimension
 */
__global__ void matmul_smem_kernel(float* __restrict__ C,
                                    const float* __restrict__ A,
                                    const float* __restrict__ B,
                                    int M, int N, int K) {
    __shared__ float As[SMEM_TILE][SMEM_TILE];
    __shared__ float Bs[SMEM_TILE][SMEM_TILE];

    int row = blockIdx.y * SMEM_TILE + threadIdx.y;
    int col = blockIdx.x * SMEM_TILE + threadIdx.x;

    float sum = 0.0f;

    for (int t = 0; t < (K + SMEM_TILE - 1) / SMEM_TILE; ++t) {
        // Load A tile
        int a_col = t * SMEM_TILE + threadIdx.x;
        if (row < M && a_col < K)
            As[threadIdx.y][threadIdx.x] = A[row * K + a_col];
        else
            As[threadIdx.y][threadIdx.x] = 0.0f;

        // Load B tile
        int b_row = t * SMEM_TILE + threadIdx.y;
        if (b_row < K && col < N)
            Bs[threadIdx.y][threadIdx.x] = B[b_row * N + col];
        else
            Bs[threadIdx.y][threadIdx.x] = 0.0f;

        __syncthreads();

        // Compute partial dot product for this tile
        for (int k = 0; k < SMEM_TILE; ++k) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

void matmul_shared_memory(float* C, const float* A, const float* B,
                           int M, int N, int K, cudaStream_t s) {
    dim3 block(SMEM_TILE, SMEM_TILE);
    dim3 grid((N + SMEM_TILE - 1) / SMEM_TILE, (M + SMEM_TILE - 1) / SMEM_TILE);
    matmul_smem_kernel<<<grid, block, 0, s>>>(C, A, B, M, N, K);
}

}  // namespace opt78
