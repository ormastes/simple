/**
 * @file 01_naive.h
 * @brief Naive matrix multiplication - baseline GPU implementation.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Naive GPU matmul: one thread per output element, no shared memory.
 *
 * Computes C = A * B where A is [M x K], B is [K x N], C is [M x N].
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
 * @performance ~50 GFLOPS on modern GPUs
 */
void matmul_naive(float* C, const float* A, const float* B,
                  int M, int N, int K, cudaStream_t s = 0);

}  // namespace opt78
