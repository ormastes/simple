/**
 * @file transformer_block.h
 * @brief Complete transformer block: attention + FFN with residual connections
 *
 * Implements a full pre-norm transformer block as used in modern LLM architectures.
 * The block consists of multi-head self-attention followed by a feed-forward network,
 * each preceded by layer normalization and wrapped with residual connections:
 *
 *   output = input + Attention(Norm(input))
 *   output = output + FFN(Norm(output))
 *
 * Supports both LayerNorm (GPT-2/BERT) and RMSNorm (LLaMA/DeepSeek) variants.
 */

#ifndef TRANSFORMER_BLOCK_H
#define TRANSFORMER_BLOCK_H

#include "layer_norm.h"
#include "rms_norm.h"
#include "feed_forward.h"
#include "common/multi_head_attention.h"  // from module 62

namespace llm {

/**
 * @brief Configuration for a transformer block
 *
 * Specifies dimensions, number of attention heads, and normalization strategy.
 */
struct TransformerBlockConfig {
    int d_model;        ///< Model dimension (embedding size)
    int num_heads;      ///< Number of attention heads
    int d_ff;           ///< Feed-forward intermediate dimension
    int max_seq_len;    ///< Maximum sequence length supported
    float dropout;      ///< Dropout rate (inference: 0.0)
    bool use_rms_norm;  ///< true = RMSNorm (LLaMA), false = LayerNorm (GPT-2)

    /**
     * @brief Construct transformer block configuration
     *
     * @param d_model      Model dimension
     * @param num_heads    Number of attention heads
     * @param d_ff         Feed-forward dimension (default: 4 * d_model)
     * @param max_seq_len  Maximum sequence length (default: 1024)
     * @param dropout      Dropout rate (default: 0.0)
     * @param use_rms_norm Whether to use RMSNorm instead of LayerNorm (default: false)
     */
    TransformerBlockConfig(int d_model, int num_heads, int d_ff = 0,
                          int max_seq_len = 1024, float dropout = 0.0f,
                          bool use_rms_norm = false)
        : d_model(d_model), num_heads(num_heads),
          d_ff(d_ff > 0 ? d_ff : 4 * d_model),
          max_seq_len(max_seq_len), dropout(dropout),
          use_rms_norm(use_rms_norm) {}
};

/**
 * @brief All weight parameters for a single transformer block
 *
 * Contains weights for self-attention, feed-forward network, and both
 * normalization layers (pre-attention and pre-FFN).
 */
struct TransformerBlockWeights {
    AttentionWeights attn;     ///< Multi-head attention weights
    FFNWeights ffn;            ///< Feed-forward network weights
    LayerNormWeights norm1;    ///< Pre-attention normalization weights
    LayerNormWeights norm2;    ///< Pre-FFN normalization weights
    float* rms_weight1;        ///< RMSNorm weight for pre-attention (if use_rms_norm)
    float* rms_weight2;        ///< RMSNorm weight for pre-FFN (if use_rms_norm)
};

/**
 * @brief Forward pass through a pre-norm transformer block
 *
 * Implements the standard pre-norm transformer architecture:
 *   1. norm_out = Norm(input)
 *   2. attn_out = MultiHeadAttention(norm_out)
 *   3. residual1 = input + attn_out
 *   4. norm_out2 = Norm(residual1)
 *   5. ffn_out = FFN(norm_out2)
 *   6. output = residual1 + ffn_out
 *
 * @param[out] output      Output tensor [batch_size, seq_len, d_model]
 * @param[in]  input       Input tensor [batch_size, seq_len, d_model]
 * @param[in]  weights     All block weight parameters
 * @param[in]  config      Block configuration
 * @param[in]  batch_size  Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  stream      CUDA stream for async execution
 *
 * @note All pointers must point to device memory
 * @note Internally allocates temporary buffers for intermediate results
 */
void transformer_block_forward(float* output, const float* input,
                              const TransformerBlockWeights& weights,
                              const TransformerBlockConfig& config,
                              int batch_size, int seq_len,
                              cudaStream_t stream = 0);

/**
 * @brief Allocate all weight parameters for a transformer block
 *
 * Allocates attention weights, FFN weights, and normalization weights
 * based on the provided configuration.
 *
 * @param config Block configuration specifying dimensions
 * @return Allocated TransformerBlockWeights
 */
TransformerBlockWeights allocate_transformer_block_weights(const TransformerBlockConfig& config);

/**
 * @brief Free all weight parameters for a transformer block
 *
 * @param weights Weights to free; all pointers set to nullptr
 * @param config  Configuration (needed to determine which norm weights to free)
 */
void free_transformer_block_weights(TransformerBlockWeights& weights,
                                    const TransformerBlockConfig& config);

/**
 * @brief CUDA kernel for element-wise vector addition
 *
 * Computes: output[i] = a[i] + b[i]
 *
 * @param[out] output Result vector [size]
 * @param[in]  a      First input vector [size]
 * @param[in]  b      Second input vector [size]
 * @param[in]  size   Number of elements
 */
__global__ void vector_add_kernel(float* output, const float* a,
                                  const float* b, int size);

} // namespace llm

#endif // TRANSFORMER_BLOCK_H
