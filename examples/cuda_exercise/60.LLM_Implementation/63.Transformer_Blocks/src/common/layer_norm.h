/**
 * @file layer_norm.h
 * @brief Layer Normalization for transformer blocks
 *
 * Implements Layer Normalization as described in "Layer Normalization" (Ba et al., 2016).
 * LayerNorm normalizes each sample independently across the feature dimension,
 * making it well-suited for transformer architectures where batch statistics
 * are unreliable due to variable sequence lengths.
 */

#ifndef LAYER_NORM_H
#define LAYER_NORM_H

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Weight parameters for Layer Normalization
 *
 * Contains the learnable scale (gamma) and shift (beta) parameters
 * that allow the network to undo normalization if needed.
 */
struct LayerNormWeights {
    float* gamma;  ///< Scale parameter [hidden_dim]
    float* beta;   ///< Shift parameter [hidden_dim]
};

/**
 * @brief Apply Layer Normalization forward pass
 *
 * Computes: output = gamma * (input - mean) / sqrt(var + eps) + beta
 *
 * Each row (of size hidden_dim) is normalized independently. This is the
 * standard normalization used in GPT-2 and BERT architectures.
 *
 * @param[out] output      Normalized output [batch_size, hidden_dim]
 * @param[in]  input       Input tensor [batch_size, hidden_dim]
 * @param[in]  gamma       Scale parameter [hidden_dim]
 * @param[in]  beta        Shift parameter [hidden_dim]
 * @param[in]  batch_size  Number of rows to normalize
 * @param[in]  hidden_dim  Feature dimension (columns per row)
 * @param[in]  eps         Small constant for numerical stability
 * @param[in]  stream      CUDA stream for async execution
 *
 * @note All pointers must point to device memory
 * @performance One thread block per row; uses shared memory reduction
 */
void layer_norm_forward(float* output, const float* input,
                       const float* gamma, const float* beta,
                       int batch_size, int hidden_dim, float eps = 1e-5f,
                       cudaStream_t stream = 0);

/**
 * @brief Allocate LayerNorm weight parameters on GPU
 *
 * Allocates gamma and beta arrays on device memory, initializing gamma
 * to ones and beta to zeros (identity transform).
 *
 * @param hidden_dim Feature dimension
 * @return Allocated LayerNormWeights with gamma=1, beta=0
 */
LayerNormWeights allocate_layer_norm_weights(int hidden_dim);

/**
 * @brief Free LayerNorm weight parameters
 *
 * @param weights Weights to free; pointers set to nullptr after freeing
 */
void free_layer_norm_weights(LayerNormWeights& weights);

/**
 * @brief CUDA kernel for Layer Normalization
 *
 * Each block processes one row. Threads cooperate via shared memory to
 * compute the mean and variance, then normalize and apply scale/shift.
 *
 * @param[out] output     Normalized output [batch_size, hidden_dim]
 * @param[in]  input      Input tensor [batch_size, hidden_dim]
 * @param[in]  gamma      Scale parameter [hidden_dim]
 * @param[in]  beta       Shift parameter [hidden_dim]
 * @param[in]  hidden_dim Feature dimension
 * @param[in]  eps        Numerical stability constant
 *
 * @note Launch config: grid(batch_size), block(min(hidden_dim, 1024))
 */
__global__ void layer_norm_kernel(float* output, const float* input,
                                  const float* gamma, const float* beta,
                                  int hidden_dim, float eps);

} // namespace llm

#endif // LAYER_NORM_H
