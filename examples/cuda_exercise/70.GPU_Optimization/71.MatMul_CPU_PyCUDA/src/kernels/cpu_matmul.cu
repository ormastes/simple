/**
 * @file cpu_matmul.cu
 * @brief CPU-based matrix multiplication implementations for baseline comparison
 *
 * This file implements various CPU matrix multiplication algorithms:
 * - Naive O(N³) implementation
 * - Cache-optimized tiled implementation
 * - Multi-threaded parallel implementation
 */

#include "cpu_matmul.h"
#include <algorithm>
#include <cmath>

#ifdef HAS_OPENMP
#include <omp.h>
#endif

/**
 * Naive CPU matrix multiplication: C = A × B
 * Time Complexity: O(M × N × K)
 *
 * @param C Output matrix [M × N]
 * @param A Input matrix [M × K]
 * @param B Input matrix [K × N]
 * @param M Number of rows in A
 * @param N Number of columns in B
 * @param K Number of columns in A (rows in B)
 */
extern "C" void cpu_matmul_naive(float* C, const float* A, const float* B,
                                  int M, int N, int K) {
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += A[i * K + k] * B[k * N + j];
            }
            C[i * N + j] = sum;
        }
    }
}

/**
 * Cache-optimized tiled matrix multiplication
 * Uses blocking to improve cache locality
 *
 * @tparam TILE_SIZE Block size (typically 32-64 for L1 cache)
 */
template<int TILE_SIZE = 64>
void cpu_matmul_tiled_impl(float* C, const float* A, const float* B,
                           int M, int N, int K) {
    // Initialize C to zero
    for (int i = 0; i < M * N; i++) {
        C[i] = 0.0f;
    }

    // Tiled multiplication
    for (int i0 = 0; i0 < M; i0 += TILE_SIZE) {
        for (int j0 = 0; j0 < N; j0 += TILE_SIZE) {
            for (int k0 = 0; k0 < K; k0 += TILE_SIZE) {
                // Process TILE_SIZE × TILE_SIZE submatrix
                int i_max = std::min(i0 + TILE_SIZE, M);
                int j_max = std::min(j0 + TILE_SIZE, N);
                int k_max = std::min(k0 + TILE_SIZE, K);

                for (int i = i0; i < i_max; i++) {
                    for (int j = j0; j < j_max; j++) {
                        float sum = C[i * N + j];
                        for (int k = k0; k < k_max; k++) {
                            sum += A[i * K + k] * B[k * N + j];
                        }
                        C[i * N + j] = sum;
                    }
                }
            }
        }
    }
}

extern "C" void cpu_matmul_tiled(float* C, const float* A, const float* B,
                                 int M, int N, int K, int tile_size) {
    if (tile_size == 32) {
        cpu_matmul_tiled_impl<32>(C, A, B, M, N, K);
    } else if (tile_size == 64) {
        cpu_matmul_tiled_impl<64>(C, A, B, M, N, K);
    } else {
        cpu_matmul_tiled_impl<64>(C, A, B, M, N, K);  // Default to 64
    }
}

/**
 * Multi-threaded parallel matrix multiplication
 * Uses OpenMP for parallelization across CPU cores
 */
extern "C" void cpu_matmul_parallel(float* C, const float* A, const float* B,
                                    int M, int N, int K, int num_threads) {
#ifdef HAS_OPENMP
    if (num_threads > 0) {
        omp_set_num_threads(num_threads);
    }

    #pragma omp parallel for collapse(2)
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += A[i * K + k] * B[k * N + j];
            }
            C[i * N + j] = sum;
        }
    }
#else
    // Fallback to naive if OpenMP not available
    cpu_matmul_naive(C, A, B, M, N, K);
#endif
}

/**
 * Matrix multiplication with performance timing
 * Returns elapsed time in milliseconds
 */
extern "C" float cpu_matmul_timed(float* C, const float* A, const float* B,
                                  int M, int N, int K, const char* method) {
    auto start = std::chrono::high_resolution_clock::now();

    if (strcmp(method, "naive") == 0) {
        cpu_matmul_naive(C, A, B, M, N, K);
    } else if (strcmp(method, "tiled") == 0) {
        cpu_matmul_tiled(C, A, B, M, N, K, 64);
    } else if (strcmp(method, "parallel") == 0) {
        cpu_matmul_parallel(C, A, B, M, N, K, -1);
    } else {
        cpu_matmul_naive(C, A, B, M, N, K);
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<float, std::milli> duration = end - start;
    return duration.count();
}
