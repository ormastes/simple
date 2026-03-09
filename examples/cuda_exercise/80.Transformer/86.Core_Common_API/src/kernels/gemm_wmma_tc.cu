/**
 * @file gemm_wmma_tc.cu
 * @brief Tensor Core WMMA GEMM implementation (fp16->fp32)
 */
#include "common/epilogue_kernels.cuh"
#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include <mma.h>

using namespace nvcuda;

namespace transformer {

/// WMMA tile dimensions (fixed by hardware)
constexpr int WMMA_M = 16;
constexpr int WMMA_N = 16;
constexpr int WMMA_K = 16;

/**
 * @brief WMMA GEMM kernel: C(fp32) = A(fp16) * B(fp16)
 *
 * Each warp computes one WMMA_M x WMMA_N output tile using Tensor Core
 * matrix multiply-accumulate instructions.
 *
 * @param[out] C Output matrix [M, N] in fp32
 * @param[in] A Input matrix [M, K] in fp16, row-major
 * @param[in] B Input matrix [K, N] in fp16, row-major
 * @param[in] M Number of rows of A and C
 * @param[in] N Number of columns of B and C
 * @param[in] K Inner dimension
 */
__global__ void wmma_gemm_kernel(float* __restrict__ C,
                                  const half* __restrict__ A,
                                  const half* __restrict__ B,
                                  int M, int N, int K) {
    int warpM = (blockIdx.y * blockDim.y + threadIdx.y);
    int warpN = (blockIdx.x * blockDim.x + threadIdx.x) / 32;

    if (warpM * WMMA_M >= M || warpN * WMMA_N >= N) return;

    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> b_frag;
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> c_frag;

    wmma::fill_fragment(c_frag, 0.0f);

    for (int k = 0; k < K; k += WMMA_K) {
        int aRow = warpM * WMMA_M;
        int aCol = k;
        int bRow = k;
        int bCol = warpN * WMMA_N;

        if (aRow < M && aCol + WMMA_K <= K && bCol < N) {
            wmma::load_matrix_sync(a_frag, A + aRow * K + aCol, K);
            wmma::load_matrix_sync(b_frag, B + bRow * N + bCol, N);
            wmma::mma_sync(c_frag, a_frag, b_frag, c_frag);
        }
    }

    int cRow = warpM * WMMA_M;
    int cCol = warpN * WMMA_N;
    if (cRow < M && cCol < N) {
        wmma::store_matrix_sync(C + cRow * N + cCol, c_frag, N, wmma::mem_row_major);
    }
}

/**
 * @brief Launch WMMA GEMM: C(fp32) = A(fp16) * B(fp16)
 * @param[out] C Output matrix [M, N] in fp32
 * @param[in] A Input matrix [M, K] in fp16
 * @param[in] B Input matrix [K, N] in fp16
 * @param[in] M Number of rows
 * @param[in] N Number of columns
 * @param[in] K Inner dimension
 * @param[in] stream CUDA stream
 */
void wmma_gemm_fp16(float* C, const half* A, const half* B,
                    int M, int N, int K, cudaStream_t stream) {
    dim3 block(128, 1);  // 4 warps per block
    dim3 grid((N + WMMA_N * 4 - 1) / (WMMA_N * 4), (M + WMMA_M - 1) / WMMA_M);
    wmma_gemm_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}

} // namespace transformer
