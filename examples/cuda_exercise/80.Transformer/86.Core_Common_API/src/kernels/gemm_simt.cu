/**
 * @file gemm_simt.cu
 * @brief Shared-memory SIMT GEMM implementation (fp32/fp16)
 */
#include "common/epilogue_kernels.cuh"
#include <cuda_runtime.h>

namespace transformer {

#define TILE_M 32
#define TILE_N 32
#define TILE_K 8

/**
 * @brief SIMT GEMM kernel: C = A * B with shared memory tiling
 * @param[out] C Output matrix [M, N]
 * @param[in] A Input matrix [M, K]
 * @param[in] B Input matrix [K, N]
 * @param[in] M Number of rows of A and C
 * @param[in] N Number of columns of B and C
 * @param[in] K Inner dimension (columns of A, rows of B)
 * @param[in] ep Epilogue configuration
 * @param[in] bias Bias vector [N] (may be nullptr)
 * @param[in] residual Residual matrix [M, N] (may be nullptr)
 */
__global__ void simt_gemm_kernel(float* __restrict__ C,
                                  const float* __restrict__ A,
                                  const float* __restrict__ B,
                                  int M, int N, int K, Epilogue ep,
                                  const float* bias, const float* residual) {
    __shared__ float As[TILE_M][TILE_K];
    __shared__ float Bs[TILE_K][TILE_N];

    int row = blockIdx.y * TILE_M + threadIdx.y;
    int col = blockIdx.x * TILE_N + threadIdx.x;

    float sum = 0.0f;

    for (int t = 0; t < (K + TILE_K - 1) / TILE_K; t++) {
        // Load tiles into shared memory
        int a_col = t * TILE_K + threadIdx.x;
        int b_row = t * TILE_K + threadIdx.y;

        if (threadIdx.x < TILE_K && row < M && a_col < K) {
            As[threadIdx.y][threadIdx.x] = A[row * K + a_col];
        } else if (threadIdx.x < TILE_K) {
            As[threadIdx.y][threadIdx.x] = 0.0f;
        }

        if (threadIdx.y < TILE_K && b_row < K && col < N) {
            Bs[threadIdx.y][threadIdx.x] = B[b_row * N + col];
        } else if (threadIdx.y < TILE_K) {
            Bs[threadIdx.y][threadIdx.x] = 0.0f;
        }

        __syncthreads();

        // Compute partial dot product
        for (int k = 0; k < TILE_K; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < M && col < N) {
        int idx = row * N + col;
        float b = (ep.has_bias && bias) ? bias[col] : 0.0f;
        float r = (ep.has_residual && residual) ? residual[idx] : 0.0f;
        C[idx] = apply_epilogue(sum, b, r, ep);
    }
}

/**
 * @brief Launch SIMT GEMM: C = A * B with fused epilogue
 * @param[out] C Output matrix [M, N]
 * @param[in] A Input matrix [M, K]
 * @param[in] B Input matrix [K, N]
 * @param[in] M Number of rows
 * @param[in] N Number of columns
 * @param[in] K Inner dimension
 * @param[in] ep Epilogue configuration
 * @param[in] bias Bias vector [N] (may be nullptr)
 * @param[in] residual Residual matrix [M, N] (may be nullptr)
 * @param[in] stream CUDA stream
 */
void simt_gemm_fp32(float* C, const float* A, const float* B,
                    int M, int N, int K, Epilogue ep,
                    const float* bias, const float* residual,
                    cudaStream_t stream) {
    dim3 block(TILE_N, TILE_M);
    dim3 grid((N + TILE_N - 1) / TILE_N, (M + TILE_M - 1) / TILE_M);
    simt_gemm_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K, ep, bias, residual);
}

#undef TILE_M
#undef TILE_N
#undef TILE_K

} // namespace transformer
