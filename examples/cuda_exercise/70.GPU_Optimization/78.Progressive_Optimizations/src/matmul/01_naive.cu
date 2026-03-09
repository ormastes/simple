/**
 * @file 01_naive.cu
 * @brief Naive matrix multiplication kernel - one element per thread, no shared memory.
 *
 * This is the baseline GPU matmul implementation. Each thread computes one element
 * of the output matrix C by iterating over the entire K dimension. Expected
 * performance is around 50 GFLOPS due to uncoalesced global memory access patterns
 * and lack of data reuse.
 */

#include "matmul/01_naive.h"
#include <cuda_runtime.h>
#include <cstdio>

namespace opt78 {

/**
 * @brief Naive matmul kernel: C[i][j] = sum_k A[i][k] * B[k][j]
 *
 * @param[out] C Output matrix [M x N]
 * @param[in]  A Input matrix [M x K]
 * @param[in]  B Input matrix [K x N]
 * @param[in]  M Rows of A / rows of C
 * @param[in]  N Cols of B / cols of C
 * @param[in]  K Cols of A / rows of B
 */
__global__ void matmul_naive_kernel(float* __restrict__ C,
                                     const float* __restrict__ A,
                                     const float* __restrict__ B,
                                     int M, int N, int K) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

void matmul_naive(float* C, const float* A, const float* B,
                  int M, int N, int K, cudaStream_t s) {
    dim3 block(16, 16);
    dim3 grid((N + block.x - 1) / block.x, (M + block.y - 1) / block.y);
    matmul_naive_kernel<<<grid, block, 0, s>>>(C, A, B, M, N, K);
}

}  // namespace opt78
