/**
 * @file gqa_attention.h
 * @brief Grouped Query Attention (GQA) interface
 *
 * Implements Grouped Query Attention as used in DeepSeek R1 and LLaMA 2/3.
 * GQA uses fewer KV heads than query heads, where each KV head is shared
 * among (num_heads / num_kv_heads) query heads. This reduces KV cache
 * memory during inference while maintaining model quality.
 */

#pragma once

#include <cuda_runtime.h>
#include "deepseek_config.h"

namespace llm {

/**
 * @brief GQA weight matrices
 *
 * Weight dimensions differ from standard MHA because Q and KV projections
 * have different output dimensions due to the head count asymmetry.
 */
struct GQAWeights {
    float* W_Q;   ///< Query projection [d_model, num_heads * head_dim]
    float* W_K;   ///< Key projection [d_model, num_kv_heads * head_dim]
    float* W_V;   ///< Value projection [d_model, num_kv_heads * head_dim]
    float* W_O;   ///< Output projection [num_heads * head_dim, d_model]
    float* b_Q;   ///< Query bias [num_heads * head_dim] (optional, nullptr if unused)
    float* b_K;   ///< Key bias [num_kv_heads * head_dim] (optional)
    float* b_V;   ///< Value bias [num_kv_heads * head_dim] (optional)
    float* b_O;   ///< Output bias [d_model] (optional)
};

/**
 * @brief Compute Grouped Query Attention forward pass
 *
 * Performs the complete GQA computation:
 * 1. Project input to Q [batch, seq, num_heads * head_dim]
 * 2. Project input to K, V [batch, seq, num_kv_heads * head_dim]
 * 3. For each group of (num_heads / num_kv_heads) query heads, share one KV head
 * 4. Compute scaled dot-product attention per group
 * 5. Concatenate all heads and project through W_O
 *
 * @param[out] output      Output tensor [batch, seq_len, d_model]
 * @param[in]  input       Input tensor [batch, seq_len, d_model]
 * @param[in]  weights     GQA weight matrices
 * @param[in]  config      DeepSeek model configuration
 * @param[in]  batch_size  Number of sequences in batch
 * @param[in]  seq_len     Current sequence length
 * @param[in]  causal      Whether to apply causal masking (default: true)
 * @param[in]  stream      CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @pre config.num_heads % config.num_kv_heads == 0
 * @performance O(batch * num_heads * seq_len^2 * head_dim) with reduced KV memory
 */
void gqa_forward(float* output, const float* input,
                 const GQAWeights& weights,
                 const DeepSeekConfig& config,
                 int batch_size, int seq_len,
                 bool causal = true,
                 cudaStream_t stream = 0);

/**
 * @brief Allocate GQA weights on device
 *
 * Allocates GPU memory for all GQA weight matrices with correct dimensions
 * for the asymmetric Q vs KV head counts.
 *
 * @param[in] config DeepSeek configuration specifying head counts
 * @return GQAWeights with allocated device pointers
 *
 * @note Caller must call free_gqa_weights() to release memory
 */
GQAWeights allocate_gqa_weights(const DeepSeekConfig& config);

/**
 * @brief Free GQA weights
 *
 * Releases all GPU memory held by the GQA weight matrices and biases.
 *
 * @param[in,out] weights Weights to free; pointers set to nullptr
 */
void free_gqa_weights(GQAWeights& weights);

/**
 * @brief Initialize GQA weights with Xavier initialization
 *
 * @param[in,out] weights Pre-allocated weights to initialize
 * @param[in]     config  DeepSeek configuration
 * @param[in]     seed    Random seed for reproducibility (default: 42)
 */
void initialize_gqa_weights(GQAWeights& weights,
                            const DeepSeekConfig& config,
                            unsigned int seed = 42);

} // namespace llm
