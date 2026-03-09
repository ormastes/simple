/**
 * @file rmsnorm.cuh
 * @brief RMSNorm kernel declarations
 *
 * Root Mean Square Layer Normalization as used in LLaMA and other modern
 * transformer architectures. Unlike LayerNorm, RMSNorm does not subtract
 * the mean, making it cheaper to compute while retaining similar quality.
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Launch RMSNorm kernel
 *
 * Computes: output[b][i] = weight[i] * input[b][i] * rsqrt(mean(input[b]^2) + eps)
 *
 * Each row (of length hidden_dim) is normalized independently.
 * One thread block is assigned per row, using block-level reduction from Module 88.
 *
 * @param[out] output Normalized output [batch_size, hidden_dim]
 * @param[in] input Input tensor [batch_size, hidden_dim]
 * @param[in] weight Learnable scale parameter [hidden_dim]
 * @param[in] batch_size Number of rows
 * @param[in] hidden_dim Number of columns (feature dimension)
 * @param[in] eps Epsilon for numerical stability (default 1e-6)
 * @param[in] stream CUDA stream
 */
void launch_rmsnorm(float* output, const float* input, const float* weight,
                    int batch_size, int hidden_dim, float eps = 1e-6f,
                    cudaStream_t stream = 0);

/**
 * @brief Launch fp16 RMSNorm kernel
 *
 * Same computation as the fp32 variant but operates on half-precision tensors.
 * Internal reduction is done in fp32 for numerical stability.
 *
 * @param[out] output Normalized output [batch_size, hidden_dim] in fp16
 * @param[in] input Input tensor [batch_size, hidden_dim] in fp16
 * @param[in] weight Learnable scale parameter [hidden_dim] in fp16
 * @param[in] batch_size Number of rows
 * @param[in] hidden_dim Number of columns (feature dimension)
 * @param[in] eps Epsilon for numerical stability (default 1e-6)
 * @param[in] stream CUDA stream
 */
void launch_rmsnorm_fp16(void* output, const void* input, const void* weight,
                         int batch_size, int hidden_dim, float eps = 1e-6f,
                         cudaStream_t stream = 0);

} // namespace transformer
