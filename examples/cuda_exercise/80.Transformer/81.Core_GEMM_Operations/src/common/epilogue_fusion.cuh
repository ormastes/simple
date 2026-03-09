/**
 * @file epilogue_fusion.cuh
 * @brief High-level epilogue fusion helpers for common neural network layers
 *
 * Provides convenience wrappers around the GEMM dispatcher for common patterns
 * such as linear layers and linear+activation fusions used throughout transformer
 * models.
 */
#pragma once
#include "gemm_ops.cuh"

namespace transformer {

/**
 * @brief Linear layer: output = input @ weights + bias
 *
 * Standard dense/fully-connected layer without activation. This is the most
 * common building block in transformer architectures (Q/K/V projections,
 * output projections, FFN layers).
 *
 * @param[out] output Result matrix [batch, out_dim]
 * @param[in] input Input matrix [batch, in_dim]
 * @param[in] weights Weight matrix [in_dim, out_dim]
 * @param[in] bias Bias vector [out_dim] (may be nullptr)
 * @param[in] batch Batch size (number of rows)
 * @param[in] in_dim Input feature dimension
 * @param[in] out_dim Output feature dimension
 * @param[in] stream CUDA stream
 */
inline void linear(float* output, const float* input, const float* weights,
                   const float* bias, int batch, int in_dim, int out_dim,
                   cudaStream_t stream = 0) {
    gemm_with_bias_act(output, input, weights, bias, batch, out_dim, in_dim, false, stream);
}

/**
 * @brief Linear layer with GELU activation: output = GELU(input @ weights + bias)
 *
 * Fused linear + GELU activation commonly used in the first layer of
 * transformer FFN blocks (GPT-2/3 style).
 *
 * @param[out] output Result matrix [batch, out_dim]
 * @param[in] input Input matrix [batch, in_dim]
 * @param[in] weights Weight matrix [in_dim, out_dim]
 * @param[in] bias Bias vector [out_dim] (may be nullptr)
 * @param[in] batch Batch size (number of rows)
 * @param[in] in_dim Input feature dimension
 * @param[in] out_dim Output feature dimension
 * @param[in] stream CUDA stream
 */
inline void linear_gelu(float* output, const float* input, const float* weights,
                        const float* bias, int batch, int in_dim, int out_dim,
                        cudaStream_t stream = 0) {
    gemm_with_bias_act(output, input, weights, bias, batch, out_dim, in_dim, true, stream);
}

} // namespace transformer
