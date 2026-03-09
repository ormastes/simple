/**
 * @file self_attention.h
 * @brief Self-attention layer interface for LLM transformer blocks
 *
 * Provides the core attention computation: scaled dot-product attention
 * as described in "Attention Is All You Need" (Vaswani et al., 2017).
 *
 * Based on "LLMs from Scratch" Chapter 3.
 */

#ifndef SELF_ATTENTION_H
#define SELF_ATTENTION_H

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Configuration for attention computation
 *
 * Holds all hyperparameters needed to set up and run attention layers.
 * The head_dim is automatically computed as d_model / num_heads.
 */
struct AttentionConfig {
    int d_model;      ///< Model dimension (total embedding size)
    int num_heads;    ///< Number of attention heads
    int head_dim;     ///< Dimension per head (d_model / num_heads)
    int max_seq_len;  ///< Maximum sequence length
    float dropout;    ///< Dropout rate (0.0 = no dropout)

    /**
     * @brief Construct attention configuration
     *
     * @param d_model    Model dimension (must be divisible by num_heads)
     * @param num_heads  Number of attention heads
     * @param max_seq_len Maximum sequence length (default: 1024)
     * @param dropout    Dropout rate (default: 0.0)
     *
     * @pre d_model % num_heads == 0
     */
    AttentionConfig(int d_model, int num_heads, int max_seq_len = 1024, float dropout = 0.0f)
        : d_model(d_model), num_heads(num_heads), head_dim(d_model / num_heads),
          max_seq_len(max_seq_len), dropout(dropout) {}
};

/**
 * @brief Self-attention weights container
 *
 * Holds device pointers to all weight matrices and biases
 * for the attention layer projections.
 */
struct AttentionWeights {
    float* W_Q;  ///< Query projection weight [d_model, d_model]
    float* W_K;  ///< Key projection weight [d_model, d_model]
    float* W_V;  ///< Value projection weight [d_model, d_model]
    float* W_O;  ///< Output projection weight [d_model, d_model]
    float* b_Q;  ///< Query bias [d_model]
    float* b_K;  ///< Key bias [d_model]
    float* b_V;  ///< Value bias [d_model]
    float* b_O;  ///< Output bias [d_model]
};

/**
 * @brief Compute scaled dot-product attention (naive, no fusion)
 *
 * Computes Attention(Q, K, V) = softmax(QK^T / sqrt(d_k)) * V
 * for each head independently. This is a reference implementation
 * prioritizing clarity over performance.
 *
 * @param[out] output  Attention output [batch, seq_len, d_model]
 * @param[in]  Q       Query tensor [batch, seq_len, d_model]
 * @param[in]  K       Key tensor [batch, seq_len, d_model]
 * @param[in]  V       Value tensor [batch, seq_len, d_model]
 * @param[in]  config  Attention configuration
 * @param[in]  batch_size Number of sequences in batch
 * @param[in]  seq_len    Sequence length
 * @param[in]  stream  CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @performance O(batch * num_heads * seq_len^2 * head_dim) FLOPs
 */
void self_attention_forward(float* output, const float* Q, const float* K, const float* V,
                           const AttentionConfig& config, int batch_size, int seq_len,
                           cudaStream_t stream = 0);

} // namespace llm

#endif // SELF_ATTENTION_H
