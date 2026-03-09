/**
 * @file 04_vectorized.cu
 * @brief Vectorized matrix multiplication using float4 loads and 2D register tiling.
 *
 * Extends the tiled approach by using vectorized (float4) loads to maximize
 * memory throughput and a larger 2D register tile per thread. This saturates
 * the memory bus more efficiently, achieving around 800 GFLOPS.
 */

#include "matmul/04_vectorized.h"
#include <cuda_runtime.h>

namespace opt78 {

/// @brief Block tile M dimension
constexpr int V_BM = 64;
/// @brief Block tile N dimension
constexpr int V_BN = 64;
/// @brief Block tile K dimension
constexpr int V_BK = 16;
/// @brief Thread tile M dimension
constexpr int V_TM = 8;
/// @brief Thread tile N dimension
constexpr int V_TN = 8;

/**
 * @brief Vectorized matmul kernel with float4 loads and 2D register tiling.
 *
 * Each thread block processes a V_BM x V_BN output tile. Shared memory is
 * loaded using float4 to achieve 128-bit memory transactions. Each thread
 * computes a V_TM x V_TN output sub-tile.
 *
 * @param[out] C Output matrix [M x N]
 * @param[in]  A Input matrix [M x K]
 * @param[in]  B Input matrix [K x N]
 * @param[in]  M Rows of A
 * @param[in]  N Cols of B
 * @param[in]  K Inner dimension
 */
__global__ void matmul_vectorized_kernel(float* __restrict__ C,
                                          const float* __restrict__ A,
                                          const float* __restrict__ B,
                                          int M, int N, int K) {
    __shared__ float As[V_BK][V_BM];
    __shared__ float Bs[V_BK][V_BN];

    constexpr int threads_per_block = (V_BM / V_TM) * (V_BN / V_TN);  // 64
    const int tid = threadIdx.x;
    const int thread_row = tid / (V_BN / V_TN);
    const int thread_col = tid % (V_BN / V_TN);

    const int block_row = blockIdx.y * V_BM;
    const int block_col = blockIdx.x * V_BN;

    float reg_c[V_TM][V_TN] = {};

    for (int bk = 0; bk < K; bk += V_BK) {
        // Vectorized load of A tile using float4 (4 floats at a time)
        for (int load_idx = tid; load_idx < (V_BM * V_BK) / 4; load_idx += threads_per_block) {
            int flat = load_idx * 4;
            int lm = flat % V_BM;
            int lk = flat / V_BM;

            int global_row = block_row + lm;
            int global_k = bk + lk;

            if (global_row + 3 < M && global_k < K) {
                // Load 4 consecutive rows of A
                As[lk][lm + 0] = A[(global_row + 0) * K + global_k];
                As[lk][lm + 1] = A[(global_row + 1) * K + global_k];
                As[lk][lm + 2] = A[(global_row + 2) * K + global_k];
                As[lk][lm + 3] = A[(global_row + 3) * K + global_k];
            } else {
                for (int i = 0; i < 4; ++i) {
                    int r = global_row + i;
                    As[lk][lm + i] = (r < M && global_k < K) ? A[r * K + global_k] : 0.0f;
                }
            }
        }

        // Vectorized load of B tile using float4
        for (int load_idx = tid; load_idx < (V_BK * V_BN) / 4; load_idx += threads_per_block) {
            int flat = load_idx * 4;
            int lk = flat / V_BN;
            int ln = flat % V_BN;

            int global_k = bk + lk;
            int global_col = block_col + ln;

            if (global_col + 3 < N && global_k < K) {
                float4 val = *reinterpret_cast<const float4*>(&B[global_k * N + global_col]);
                Bs[lk][ln + 0] = val.x;
                Bs[lk][ln + 1] = val.y;
                Bs[lk][ln + 2] = val.z;
                Bs[lk][ln + 3] = val.w;
            } else {
                for (int i = 0; i < 4; ++i) {
                    int c = global_col + i;
                    Bs[lk][ln + i] = (global_k < K && c < N) ? B[global_k * N + c] : 0.0f;
                }
            }
        }

        __syncthreads();

        // Register-blocked computation
        #pragma unroll
        for (int k = 0; k < V_BK; ++k) {
            float a_reg[V_TM];
            float b_reg[V_TN];

            #pragma unroll
            for (int tm = 0; tm < V_TM; ++tm)
                a_reg[tm] = As[k][thread_row * V_TM + tm];

            #pragma unroll
            for (int tn = 0; tn < V_TN; ++tn)
                b_reg[tn] = Bs[k][thread_col * V_TN + tn];

            #pragma unroll
            for (int tm = 0; tm < V_TM; ++tm) {
                #pragma unroll
                for (int tn = 0; tn < V_TN; ++tn) {
                    reg_c[tm][tn] += a_reg[tm] * b_reg[tn];
                }
            }
        }

        __syncthreads();
    }

    // Write results back using vectorized stores where possible
    #pragma unroll
    for (int tm = 0; tm < V_TM; ++tm) {
        int global_row = block_row + thread_row * V_TM + tm;
        if (global_row >= M) continue;

        #pragma unroll
        for (int tn = 0; tn < V_TN; tn += 4) {
            int global_col = block_col + thread_col * V_TN + tn;
            if (global_col + 3 < N) {
                float4 out;
                out.x = reg_c[tm][tn + 0];
                out.y = reg_c[tm][tn + 1];
                out.z = reg_c[tm][tn + 2];
                out.w = reg_c[tm][tn + 3];
                *reinterpret_cast<float4*>(&C[global_row * N + global_col]) = out;
            } else {
                for (int i = 0; i < 4; ++i) {
                    int c = global_col + i;
                    if (c < N) C[global_row * N + c] = reg_c[tm][tn + i];
                }
            }
        }
    }
}

void matmul_vectorized(float* C, const float* A, const float* B,
                        int M, int N, int K, cudaStream_t s) {
    constexpr int threads = (V_BM / V_TM) * (V_BN / V_TN);  // 64
    dim3 block(threads);
    dim3 grid((N + V_BN - 1) / V_BN, (M + V_BM - 1) / V_BM);
    matmul_vectorized_kernel<<<grid, block, 0, s>>>(C, A, B, M, N, K);
}

}  // namespace opt78
