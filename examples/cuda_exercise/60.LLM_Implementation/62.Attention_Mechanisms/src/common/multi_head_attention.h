/**
 * @file multi_head_attention.h
 * @brief Multi-head attention with QKV projections
 *
 * Implements the complete multi-head attention mechanism: projects input
 * to Q, K, V using learned weight matrices, computes attention per head,
 * concatenates heads, and applies output projection.
 *
 * Based on "LLMs from Scratch" Chapter 3.
 */

#ifndef MULTI_HEAD_ATTENTION_H
#define MULTI_HEAD_ATTENTION_H

#include "self_attention.h"

namespace llm {

/**
 * @brief Multi-head attention: projects input to Q,K,V, computes attention, projects output
 *
 * Performs the complete multi-head attention computation:
 * 1. Project input to Q, K, V using W_Q, W_K, W_V
 * 2. Split into num_heads heads
 * 3. Compute scaled dot-product attention per head (with optional causal mask)
 * 4. Concatenate heads
 * 5. Project through W_O
 *
 * @param[out] output     Output tensor [batch, seq_len, d_model]
 * @param[in]  input      Input tensor [batch, seq_len, d_model]
 * @param[in]  weights    Attention weights (W_Q, W_K, W_V, W_O, biases)
 * @param[in]  config     Attention configuration
 * @param[in]  batch_size Number of sequences in batch
 * @param[in]  seq_len    Sequence length
 * @param[in]  causal     Whether to use causal masking (default: true)
 * @param[in]  stream     CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @performance O(batch * seq_len * d_model^2 + batch * num_heads * seq_len^2 * head_dim)
 */
void multi_head_attention_forward(float* output, const float* input,
                                 const AttentionWeights& weights,
                                 const AttentionConfig& config,
                                 int batch_size, int seq_len,
                                 bool causal = true,
                                 cudaStream_t stream = 0);

/**
 * @brief Allocate attention weights on device
 *
 * Allocates GPU memory for all weight matrices and bias vectors
 * required by multi-head attention.
 *
 * @param config Attention configuration specifying d_model
 * @return AttentionWeights with allocated device pointers
 *
 * @note Caller is responsible for calling free_attention_weights()
 * @note Weights are NOT initialized; use initialize_attention_weights()
 */
AttentionWeights allocate_attention_weights(const AttentionConfig& config);

/**
 * @brief Free attention weights
 *
 * Releases all GPU memory held by the attention weight matrices and biases.
 *
 * @param[in,out] weights Weights to free; pointers set to nullptr after free
 */
void free_attention_weights(AttentionWeights& weights);

/**
 * @brief Initialize attention weights with Xavier initialization
 *
 * Fills weight matrices with values drawn from N(0, sqrt(2 / (fan_in + fan_out)))
 * and biases with zeros.
 *
 * @param[in,out] weights Pre-allocated weights to initialize
 * @param[in]     config  Attention configuration
 * @param[in]     seed    Random seed for reproducibility (default: 42)
 */
void initialize_attention_weights(AttentionWeights& weights,
                                  const AttentionConfig& config,
                                  unsigned int seed = 42);

} // namespace llm

#endif // MULTI_HEAD_ATTENTION_H
