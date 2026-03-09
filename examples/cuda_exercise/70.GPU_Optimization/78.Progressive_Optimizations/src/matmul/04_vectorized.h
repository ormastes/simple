/**
 * @file 04_vectorized.h
 * @brief Vectorized matrix multiplication using float4 loads and 2D register tiling.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Vectorized GPU matmul with float4 loads and 8x8 register tiles per thread.
 *
 * Computes C = A * B using vectorized memory access patterns for maximum bandwidth
 * utilization. All pointers must refer to device memory.
 *
 * @param[out] C Output matrix [M x N] (device)
 * @param[in]  A Input matrix [M x K] (device)
 * @param[in]  B Input matrix [K x N] (device)
 * @param[in]  M Rows of A
 * @param[in]  N Columns of B
 * @param[in]  K Inner dimension
 * @param[in]  s CUDA stream (default 0)
 *
 * @performance ~800 GFLOPS on modern GPUs
 */
void matmul_vectorized(float* C, const float* A, const float* B,
                        int M, int N, int K, cudaStream_t s = 0);

}  // namespace opt78
