/**
 * @file 03_tiled.h
 * @brief 32x32 tiled matrix multiplication with register blocking and loop unrolling.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Tiled GPU matmul with 32x32 tiles, register blocking (4x4), and loop unrolling.
 *
 * Computes C = A * B with improved arithmetic intensity through register-level
 * data reuse. All pointers must refer to device memory.
 *
 * @param[out] C Output matrix [M x N] (device)
 * @param[in]  A Input matrix [M x K] (device)
 * @param[in]  B Input matrix [K x N] (device)
 * @param[in]  M Rows of A
 * @param[in]  N Columns of B
 * @param[in]  K Inner dimension
 * @param[in]  s CUDA stream (default 0)
 *
 * @performance ~500 GFLOPS on modern GPUs
 */
void matmul_tiled(float* C, const float* A, const float* B,
                  int M, int N, int K, cudaStream_t s = 0);

}  // namespace opt78
