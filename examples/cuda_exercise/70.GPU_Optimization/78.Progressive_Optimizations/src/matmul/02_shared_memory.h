/**
 * @file 02_shared_memory.h
 * @brief Shared memory tiled matrix multiplication with 16x16 tiles.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Shared memory tiled GPU matmul with 16x16 tiles.
 *
 * Computes C = A * B using shared memory tiling to reduce global memory traffic.
 * All pointers must refer to device memory.
 *
 * @param[out] C Output matrix [M x N] (device)
 * @param[in]  A Input matrix [M x K] (device)
 * @param[in]  B Input matrix [K x N] (device)
 * @param[in]  M Rows of A
 * @param[in]  N Columns of B
 * @param[in]  K Inner dimension
 * @param[in]  s CUDA stream (default 0)
 *
 * @performance ~200 GFLOPS on modern GPUs
 */
void matmul_shared_memory(float* C, const float* A, const float* B,
                           int M, int N, int K, cudaStream_t s = 0);

}  // namespace opt78
