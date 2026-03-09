/**
 * @file 05_wmma.h
 * @brief Tensor Core WMMA matrix multiplication with fp16 inputs and fp32 accumulation.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Tensor Core WMMA matmul: fp16 inputs, fp32 accumulation.
 *
 * Computes C = A * B using Tensor Cores via the WMMA API. Input matrices are
 * internally converted from fp32 to fp16. Requires Volta or later architecture.
 * Dimensions should ideally be multiples of 16 for best performance.
 * All pointers must refer to device memory.
 *
 * @param[out] C Output matrix [M x N] (device, fp32)
 * @param[in]  A Input matrix [M x K] (device, fp32 - converted internally)
 * @param[in]  B Input matrix [K x N] (device, fp32 - converted internally)
 * @param[in]  M Rows of A
 * @param[in]  N Columns of B
 * @param[in]  K Inner dimension
 * @param[in]  s CUDA stream (default 0)
 *
 * @note Requires GPU with Tensor Cores (sm_70+)
 * @performance ~1200+ GFLOPS on Tensor Core GPUs
 */
void matmul_wmma(float* C, const float* A, const float* B,
                 int M, int N, int K, cudaStream_t s = 0);

}  // namespace opt78
