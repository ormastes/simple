/**
 * @file 03_tiled.cu
 * @brief 32x32 tiled matrix multiplication with loop unrolling and register blocking.
 *
 * Builds on the shared memory approach by using larger tiles (32x32), explicit
 * loop unrolling, and register-level data reuse. Each thread computes a small
 * sub-tile of the output (TM x TN elements) to increase arithmetic intensity.
 * Expected performance is around 500 GFLOPS.
 */

#include "matmul/03_tiled.h"
#include <cuda_runtime.h>

namespace opt78 {

/// @brief Block tile dimension
constexpr int BM = 32;
/// @brief Block tile dimension (N direction)
constexpr int BN = 32;
/// @brief Block tile dimension (K direction)
constexpr int BK = 32;
/// @brief Thread tile dimension (M direction)
constexpr int TM = 4;
/// @brief Thread tile dimension (N direction)
constexpr int TN = 4;

/**
 * @brief Tiled matmul kernel with register blocking.
 *
 * Each thread block processes a BM x BN output tile. Each thread computes
 * a TM x TN sub-tile, reusing data from shared memory in registers for
 * higher arithmetic intensity.
 *
 * @param[out] C Output matrix [M x N]
 * @param[in]  A Input matrix [M x K]
 * @param[in]  B Input matrix [K x N]
 * @param[in]  M Rows of A
 * @param[in]  N Cols of B
 * @param[in]  K Inner dimension
 */
__global__ void matmul_tiled_kernel(float* __restrict__ C,
                                     const float* __restrict__ A,
                                     const float* __restrict__ B,
                                     int M, int N, int K) {
    __shared__ float As[BK][BM];  // Transposed for bank-conflict-free access
    __shared__ float Bs[BK][BN];

    // Thread indices within the block
    const int threads_per_block = (BM / TM) * (BN / TN);
    const int tid = threadIdx.x;
    const int thread_row = tid / (BN / TN);
    const int thread_col = tid % (BN / TN);

    // Block starting positions
    const int block_row = blockIdx.y * BM;
    const int block_col = blockIdx.x * BN;

    // Register tile for accumulation
    float reg_c[TM][TN] = {};

    // Loop over K-dimension tiles
    for (int bk = 0; bk < K; bk += BK) {
        // Cooperative loading of A tile into shared memory (transposed)
        for (int load_idx = tid; load_idx < BM * BK; load_idx += threads_per_block) {
            int lm = load_idx % BM;
            int lk = load_idx / BM;
            int global_row = block_row + lm;
            int global_k = bk + lk;
            As[lk][lm] = (global_row < M && global_k < K) ? A[global_row * K + global_k] : 0.0f;
        }

        // Cooperative loading of B tile
        for (int load_idx = tid; load_idx < BK * BN; load_idx += threads_per_block) {
            int lk = load_idx / BN;
            int ln = load_idx % BN;
            int global_k = bk + lk;
            int global_col = block_col + ln;
            Bs[lk][ln] = (global_k < K && global_col < N) ? B[global_k * N + global_col] : 0.0f;
        }

        __syncthreads();

        // Compute partial results using register blocking
        #pragma unroll
        for (int k = 0; k < BK; ++k) {
            // Load A values into registers
            float a_reg[TM];
            #pragma unroll
            for (int tm = 0; tm < TM; ++tm) {
                a_reg[tm] = As[k][thread_row * TM + tm];
            }

            // Load B values and accumulate
            #pragma unroll
            for (int tn = 0; tn < TN; ++tn) {
                float b_val = Bs[k][thread_col * TN + tn];
                #pragma unroll
                for (int tm = 0; tm < TM; ++tm) {
                    reg_c[tm][tn] += a_reg[tm] * b_val;
                }
            }
        }

        __syncthreads();
    }

    // Write results back to global memory
    #pragma unroll
    for (int tm = 0; tm < TM; ++tm) {
        int global_row = block_row + thread_row * TM + tm;
        if (global_row >= M) continue;
        #pragma unroll
        for (int tn = 0; tn < TN; ++tn) {
            int global_col = block_col + thread_col * TN + tn;
            if (global_col < N) {
                C[global_row * N + global_col] = reg_c[tm][tn];
            }
        }
    }
}

void matmul_tiled(float* C, const float* A, const float* B,
                  int M, int N, int K, cudaStream_t s) {
    constexpr int threads = (BM / TM) * (BN / TN);  // 64 threads per block
    dim3 block(threads);
    dim3 grid((N + BN - 1) / BN, (M + BM - 1) / BM);
    matmul_tiled_kernel<<<grid, block, 0, s>>>(C, A, B, M, N, K);
}

}  // namespace opt78
