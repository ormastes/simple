/**
 * @file causal_attention.h
 * @brief Causal (autoregressive) attention with future token masking
 *
 * Implements causal self-attention where each token can only attend to
 * previous tokens and itself. This is the standard attention mechanism
 * used in autoregressive language models like GPT.
 *
 * Based on "LLMs from Scratch" Chapter 3.
 */

#ifndef CAUSAL_ATTENTION_H
#define CAUSAL_ATTENTION_H

#include "self_attention.h"

namespace llm {

/**
 * @brief Compute causal self-attention (masks future positions)
 *
 * Similar to self_attention_forward but applies a causal mask so that
 * position i can only attend to positions j <= i. Future positions are
 * masked with -infinity before softmax, ensuring zero attention weight.
 *
 * @param[out] output     Attention output [batch, seq_len, d_model]
 * @param[in]  Q          Query tensor [batch, seq_len, d_model]
 * @param[in]  K          Key tensor [batch, seq_len, d_model]
 * @param[in]  V          Value tensor [batch, seq_len, d_model]
 * @param[in]  config     Attention configuration
 * @param[in]  batch_size Number of sequences in batch
 * @param[in]  seq_len    Sequence length
 * @param[in]  stream     CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @note The causal mask is: mask[i][j] = (j <= i) ? 0 : -inf
 */
void causal_attention_forward(float* output, const float* Q, const float* K, const float* V,
                             const AttentionConfig& config, int batch_size, int seq_len,
                             cudaStream_t stream = 0);

} // namespace llm

#endif // CAUSAL_ATTENTION_H
