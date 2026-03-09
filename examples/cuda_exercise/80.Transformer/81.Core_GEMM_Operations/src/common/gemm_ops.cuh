/**
 * @file gemm_ops.cuh
 * @brief High-level GEMM dispatcher that auto-selects SIMT or WMMA backend
 *
 * Provides a unified entry point for matrix multiplication operations,
 * automatically routing to the best available backend (Tensor Core WMMA
 * for fp16, shared-memory SIMT for fp32) based on input types and hardware.
 */
#pragma once
#include <cuda_runtime.h>
#include <cuda_fp16.h>

namespace transformer {

/**
 * @brief Parameters for the unified GEMM dispatcher
 *
 * Set either fp32 or fp16 input pointers depending on the desired precision.
 * When use_tensor_cores is true and fp16 pointers are set, the WMMA backend
 * is selected; otherwise the SIMT fp32 fallback is used.
 */
struct GemmParams {
    int M, N, K;              ///< Matrix dimensions: C[M,N] = A[M,K] * B[K,N]
    const float* A_fp32;      ///< fp32 input A (may be nullptr)
    const half* A_fp16;       ///< fp16 input A (may be nullptr)
    const float* B_fp32;      ///< fp32 input B (may be nullptr)
    const half* B_fp16;       ///< fp16 input B (may be nullptr)
    float* C;                 ///< Output C in fp32
    bool use_tensor_cores;    ///< Prefer Tensor Core WMMA when available
    cudaStream_t stream;      ///< CUDA stream for async execution
};

/**
 * @brief Dispatch GEMM based on params (auto-selects SIMT vs WMMA)
 * @param[in] params GEMM configuration including dimensions, pointers, and backend preference
 */
void gemm(const GemmParams& params);

/**
 * @brief GEMM with fused bias addition and optional GELU activation
 *
 * Computes C = act(A @ B + bias) where act is GELU when use_gelu is true,
 * identity otherwise. Bias is broadcast along columns (one value per output column).
 *
 * @param[out] C Output matrix [M, N]
 * @param[in] A Input matrix [M, K]
 * @param[in] B Weight matrix [K, N]
 * @param[in] bias Bias vector [N] (may be nullptr for no bias)
 * @param[in] M Number of rows
 * @param[in] N Number of columns
 * @param[in] K Inner dimension
 * @param[in] use_gelu Apply GELU activation after bias
 * @param[in] stream CUDA stream
 */
void gemm_with_bias_act(float* C, const float* A, const float* B,
                        const float* bias, int M, int N, int K,
                        bool use_gelu, cudaStream_t stream = 0);

} // namespace transformer
