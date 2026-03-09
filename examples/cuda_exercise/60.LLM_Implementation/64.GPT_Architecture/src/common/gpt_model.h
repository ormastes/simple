/**
 * @file gpt_model.h
 * @brief GPT model forward pass interface
 *
 * Defines the GPT model weights structure and forward pass that chains
 * together token/position embeddings, transformer blocks, final layer
 * normalization, and the LM head (with weight tying).
 *
 * Based on "LLMs from Scratch" Chapter 4.
 */

#pragma once

#include <cuda_runtime.h>
#include "gpt_config.h"
#include "common/self_attention.h"   // from module 62 - AttentionConfig, AttentionWeights
#include "common/layer_norm.h"       // from module 63 - LayerNormWeights

namespace llm {

/**
 * @brief Feed-forward network weights for one transformer layer
 *
 * Holds the two linear layer weights and biases for the position-wise
 * feed-forward network: FFN(x) = W2 * GELU(W1 * x + b1) + b2
 */
struct FFNWeights {
    float* W1;  ///< First linear weight [d_model, d_ff]
    float* b1;  ///< First linear bias [d_ff]
    float* W2;  ///< Second linear weight [d_ff, d_model]
    float* b2;  ///< Second linear bias [d_model]
};

/**
 * @brief Complete weights for one transformer block
 *
 * Contains multi-head attention weights, feed-forward network weights,
 * and two layer normalization parameter sets (pre-attention and pre-FFN).
 */
struct TransformerBlockWeights {
    AttentionWeights attention;  ///< Multi-head attention weights
    LayerNormWeights norm1;      ///< Pre-attention layer norm
    FFNWeights ffn;              ///< Feed-forward network weights
    LayerNormWeights norm2;      ///< Pre-FFN layer norm
};

/**
 * @brief Complete GPT model weights
 *
 * Contains all learnable parameters for the GPT model. The LM head
 * shares weights with token_embeddings (weight tying), so no separate
 * LM head weight matrix is stored.
 */
struct GPTModelWeights {
    float* token_embeddings;    ///< [vocab_size, d_model]
    float* position_embeddings; ///< [max_seq_len, d_model]
    TransformerBlockWeights* layers;  ///< Array of num_layers blocks
    LayerNormWeights final_norm;      ///< Final layer normalization
    // LM head shares weights with token_embeddings (weight tying)
};

/**
 * @brief GPT language model
 *
 * Implements the complete GPT architecture with configurable size.
 * The forward pass computes logits over the vocabulary for each position
 * in the input sequence, suitable for next-token prediction.
 *
 * @code
 * GPTModel model;
 * model.config = gpt_tiny();
 * model.allocate();
 * model.forward(logits, input_ids, batch_size, seq_len);
 * model.deallocate();
 * @endcode
 */
struct GPTModel {
    GPTConfig config;       ///< Model configuration
    GPTModelWeights weights; ///< All model weights

    /**
     * @brief Allocate all model weights on device
     *
     * Allocates GPU memory for all weight tensors and initializes them
     * with small random values (Xavier initialization).
     *
     * @pre config must be set before calling
     * @post All weight pointers in weights are valid device pointers
     */
    void allocate();

    /**
     * @brief Free all model weights
     *
     * Releases all GPU memory held by the model weights.
     *
     * @post All weight pointers are set to nullptr
     */
    void deallocate();

    /**
     * @brief Count total parameters
     *
     * @return Number of learnable parameters in the model
     */
    long long num_parameters() const;

    /**
     * @brief Forward pass: input_ids -> logits
     *
     * Computes the full GPT forward pass:
     * 1. Look up token embeddings
     * 2. Add position embeddings
     * 3. Run through each transformer block (attention + FFN + residual + norm)
     * 4. Apply final layer norm
     * 5. Compute logits via matmul with token_embeddings^T (weight tying)
     *
     * @param[out] logits     Output logits [batch_size, seq_len, vocab_size]
     * @param[in]  input_ids  Input token IDs [batch_size, seq_len]
     * @param[in]  batch_size Number of sequences in the batch
     * @param[in]  seq_len    Length of each sequence
     * @param[in]  stream     CUDA stream (default: 0)
     *
     * @note All pointers must be device memory
     * @note Caller must allocate logits with size batch_size * seq_len * vocab_size
     */
    void forward(float* logits, const int* input_ids,
                int batch_size, int seq_len, cudaStream_t stream = 0);
};

} // namespace llm
