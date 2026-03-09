/**
 * @file activation.cuh
 * @brief GPU activation function declarations for MLP layers
 *
 * Provides standalone activation kernels (GELU, SiLU, SwiGLU) for cases
 * where the activation cannot be fused into a GEMM epilogue, such as
 * gated projections in LLaMA-style feed-forward networks.
 */
#pragma once
#include <cuda_runtime.h>
#include <cuda_fp16.h>

namespace transformer {

/**
 * @brief Launch GELU activation: output[i] = x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 * @param[out] output Result array [n]
 * @param[in] input Input array [n]
 * @param[in] n Number of elements
 * @param[in] stream CUDA stream
 */
void launch_gelu(float* output, const float* input, int n, cudaStream_t stream = 0);

/**
 * @brief Launch SiLU (Swish) activation: output[i] = x / (1 + exp(-x))
 * @param[out] output Result array [n]
 * @param[in] input Input array [n]
 * @param[in] n Number of elements
 * @param[in] stream CUDA stream
 */
void launch_silu(float* output, const float* input, int n, cudaStream_t stream = 0);

/**
 * @brief Launch SwiGLU activation: output[i] = gate[i] * SiLU(x[i])
 *
 * Input is split in half: first half is x, second half is gate.
 * Output size is n/2.
 *
 * @param[out] output Result array [n/2]
 * @param[in] input Input array [n] (first half = x, second half = gate)
 * @param[in] n Total number of input elements (must be even)
 * @param[in] stream CUDA stream
 */
void launch_swiglu(float* output, const float* input, int n, cudaStream_t stream = 0);

/**
 * @brief Launch fp16 GELU activation
 * @param[out] output Result array [n] in fp16
 * @param[in] input Input array [n] in fp16
 * @param[in] n Number of elements
 * @param[in] stream CUDA stream
 */
void launch_gelu_fp16(half* output, const half* input, int n, cudaStream_t stream = 0);

} // namespace transformer
