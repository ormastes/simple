/**
 * @file epilogue_kernels.cuh
 * @brief Fused bias, activation, and residual store for GEMM epilogues
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Activation function type for GEMM epilogue
 */
enum class Activation {
    None,   ///< No activation
    GELU,   ///< Gaussian Error Linear Unit
    SiLU,   ///< Sigmoid Linear Unit (Swish)
    ReLU    ///< Rectified Linear Unit
};

/**
 * @brief Epilogue configuration for fused operations after GEMM
 */
struct Epilogue {
    bool has_bias;       ///< Add bias vector
    bool has_residual;   ///< Add residual connection
    Activation act;      ///< Activation function
    float scale;         ///< Output scaling factor

    __host__ __device__ Epilogue()
        : has_bias(false), has_residual(false), act(Activation::None), scale(1.0f) {}
};

/**
 * @brief Apply GELU activation
 */
__device__ __forceinline__ float gelu(float x) {
    const float kSqrt2OverPi = 0.7978845608028654f;  // sqrt(2/pi)
    float cdf = 0.5f * (1.0f + tanhf(kSqrt2OverPi * (x + 0.044715f * x * x * x)));
    return x * cdf;
}

/**
 * @brief Apply SiLU (Swish) activation
 */
__device__ __forceinline__ float silu(float x) {
    return x / (1.0f + expf(-x));
}

/**
 * @brief Apply activation function
 */
__device__ __forceinline__ float apply_activation(float x, Activation act) {
    switch (act) {
        case Activation::GELU: return gelu(x);
        case Activation::SiLU: return silu(x);
        case Activation::ReLU: return fmaxf(0.0f, x);
        default: return x;
    }
}

/**
 * @brief Apply full epilogue: scale * act(value + bias) + residual
 */
__device__ __forceinline__ float apply_epilogue(float value, float bias, float residual, const Epilogue& ep) {
    float result = value;
    if (ep.has_bias) result += bias;
    result = apply_activation(result, ep.act);
    result *= ep.scale;
    if (ep.has_residual) result += residual;
    return result;
}

/**
 * @brief Epilogue kernel: applies bias + activation + residual to GEMM output
 * @param[in,out] C GEMM output matrix [M, N]
 * @param[in] bias Bias vector [N] (may be nullptr)
 * @param[in] residual Residual matrix [M, N] (may be nullptr)
 * @param[in] M Number of rows
 * @param[in] N Number of columns
 * @param[in] ep Epilogue configuration
 */
static __global__ void epilogue_kernel(float* C, const float* bias, const float* residual,
                                       int M, int N, Epilogue ep) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= M * N) return;

    int col = idx % N;
    float b = (ep.has_bias && bias) ? bias[col] : 0.0f;
    float r = (ep.has_residual && residual) ? residual[idx] : 0.0f;

    C[idx] = apply_epilogue(C[idx], b, r, ep);
}

} // namespace transformer
