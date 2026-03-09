/**
 * @file gemm_ops.cu
 * @brief GEMM dispatcher implementation
 *
 * Routes GEMM calls to the appropriate backend from Module 86 (Core_Common_API):
 * - WMMA Tensor Core backend for fp16 inputs
 * - SIMT shared-memory backend for fp32 inputs
 * Both backends support fused epilogue operations (bias, activation, residual).
 */
#include "common/gemm_ops.cuh"
#include "common/epilogue_kernels.cuh"  // from 86_Core_Common_API
#include <cuda_runtime.h>

namespace transformer {

// Forward declarations of backend functions (defined in module 86)
extern void simt_gemm_fp32(float* C, const float* A, const float* B,
                           int M, int N, int K, Epilogue ep,
                           const float* bias, const float* residual,
                           cudaStream_t stream);
extern void wmma_gemm_fp16(float* C, const half* A, const half* B,
                           int M, int N, int K, cudaStream_t stream);

void gemm(const GemmParams& params) {
    if (params.use_tensor_cores && params.A_fp16 && params.B_fp16) {
        wmma_gemm_fp16(params.C, params.A_fp16, params.B_fp16,
                       params.M, params.N, params.K, params.stream);
    } else if (params.A_fp32 && params.B_fp32) {
        Epilogue ep;
        simt_gemm_fp32(params.C, params.A_fp32, params.B_fp32,
                       params.M, params.N, params.K, ep, nullptr, nullptr, params.stream);
    }
}

void gemm_with_bias_act(float* C, const float* A, const float* B,
                        const float* bias, int M, int N, int K,
                        bool use_gelu, cudaStream_t stream) {
    Epilogue ep;
    ep.has_bias = (bias != nullptr);
    ep.act = use_gelu ? Activation::GELU : Activation::None;
    simt_gemm_fp32(C, A, B, M, N, K, ep, bias, nullptr, stream);
}

} // namespace transformer
