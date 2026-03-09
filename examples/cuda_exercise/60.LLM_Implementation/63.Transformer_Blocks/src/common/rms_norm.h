/**
 * @file rms_norm.h
 * @brief RMS Normalization (used in LLaMA/DeepSeek architectures)
 *
 * Implements Root Mean Square Layer Normalization as described in
 * "Root Mean Square Layer Normalization" (Zhang & Sennrich, 2019).
 * RMSNorm omits the mean-centering step of LayerNorm, reducing
 * computation while maintaining similar performance in practice.
 */

#ifndef RMS_NORM_H
#define RMS_NORM_H

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Apply RMS Normalization forward pass
 *
 * Computes: output = weight * input * rsqrt(mean(input^2) + eps)
 *
 * Unlike LayerNorm, RMSNorm does not subtract the mean or add a bias term.
 * This makes it computationally cheaper while retaining the key benefit
 * of re-scaling invariance.
 *
 * @param[out] output      Normalized output [batch_size, hidden_dim]
 * @param[in]  input       Input tensor [batch_size, hidden_dim]
 * @param[in]  weight      Scale parameter [hidden_dim]
 * @param[in]  batch_size  Number of rows to normalize
 * @param[in]  hidden_dim  Feature dimension (columns per row)
 * @param[in]  eps         Small constant for numerical stability
 * @param[in]  stream      CUDA stream for async execution
 *
 * @note All pointers must point to device memory
 * @performance One thread block per row; uses shared memory reduction
 */
void rms_norm_forward(float* output, const float* input, const float* weight,
                     int batch_size, int hidden_dim, float eps = 1e-6f,
                     cudaStream_t stream = 0);

/**
 * @brief Allocate RMSNorm weight parameter on GPU
 *
 * Allocates weight array on device memory, initialized to ones.
 *
 * @param hidden_dim Feature dimension
 * @return Device pointer to weight array [hidden_dim], initialized to 1.0
 */
float* allocate_rms_norm_weights(int hidden_dim);

/**
 * @brief Free RMSNorm weight parameter
 *
 * @param weight Weight pointer to free; set to nullptr after freeing
 */
void free_rms_norm_weights(float*& weight);

/**
 * @brief CUDA kernel for RMS Normalization
 *
 * Each block processes one row. Threads cooperate via shared memory to
 * compute the sum of squares, then normalize and apply the weight.
 *
 * @param[out] output     Normalized output [batch_size, hidden_dim]
 * @param[in]  input      Input tensor [batch_size, hidden_dim]
 * @param[in]  weight     Scale parameter [hidden_dim]
 * @param[in]  hidden_dim Feature dimension
 * @param[in]  eps        Numerical stability constant
 *
 * @note Launch config: grid(batch_size), block(min(hidden_dim, 1024))
 */
__global__ void rms_norm_kernel(float* output, const float* input,
                                const float* weight,
                                int hidden_dim, float eps);

} // namespace llm

#endif // RMS_NORM_H
