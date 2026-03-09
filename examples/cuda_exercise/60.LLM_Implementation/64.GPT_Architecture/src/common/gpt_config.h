/**
 * @file gpt_config.h
 * @brief GPT model configuration presets
 *
 * Provides configuration structs and factory functions for various GPT-2
 * model sizes, from tiny (for testing) to large (774M parameters).
 * Also includes a parameter counting utility.
 *
 * Based on "LLMs from Scratch" Chapter 4.
 */

#pragma once

namespace llm {

/**
 * @brief Configuration for a GPT model
 *
 * Holds all hyperparameters needed to define a GPT architecture.
 * Default values correspond to GPT-2 Small (124M parameters).
 */
struct GPTConfig {
    int vocab_size;    ///< Vocabulary size
    int d_model;       ///< Model/embedding dimension
    int num_heads;     ///< Number of attention heads
    int num_layers;    ///< Number of transformer layers
    int d_ff;          ///< Feed-forward intermediate dimension
    int max_seq_len;   ///< Maximum sequence length
    float dropout;     ///< Dropout rate

    /**
     * @brief Default constructor with GPT-2 Small configuration
     */
    GPTConfig() : vocab_size(50257), d_model(768), num_heads(12),
                  num_layers(12), d_ff(3072), max_seq_len(1024), dropout(0.1f) {}
};

/// GPT-2 Small: 124M parameters (768d, 12L, 12H)
inline GPTConfig gpt2_small() {
    GPTConfig c;
    c.vocab_size = 50257; c.d_model = 768; c.num_heads = 12;
    c.num_layers = 12; c.d_ff = 3072; c.max_seq_len = 1024; c.dropout = 0.1f;
    return c;
}

/// GPT-2 Medium: 355M parameters (1024d, 24L, 16H)
inline GPTConfig gpt2_medium() {
    GPTConfig c;
    c.vocab_size = 50257; c.d_model = 1024; c.num_heads = 16;
    c.num_layers = 24; c.d_ff = 4096; c.max_seq_len = 1024; c.dropout = 0.1f;
    return c;
}

/// GPT-2 Large: 774M parameters (1280d, 36L, 20H)
inline GPTConfig gpt2_large() {
    GPTConfig c;
    c.vocab_size = 50257; c.d_model = 1280; c.num_heads = 20;
    c.num_layers = 36; c.d_ff = 5120; c.max_seq_len = 1024; c.dropout = 0.1f;
    return c;
}

/// Tiny config for testing: small enough to run on any GPU
inline GPTConfig gpt_tiny() {
    GPTConfig c;
    c.vocab_size = 256; c.d_model = 64; c.num_heads = 4;
    c.num_layers = 2; c.d_ff = 256; c.max_seq_len = 128; c.dropout = 0.0f;
    return c;
}

/**
 * @brief Count total parameters for a GPT config
 *
 * Computes the total number of learnable parameters in the model,
 * including embeddings, transformer layers, and final layer norm.
 * The LM head shares weights with token embeddings (weight tying).
 *
 * @param c GPT configuration
 * @return Total parameter count
 */
inline long long count_parameters(const GPTConfig& c) {
    long long params = 0;
    // Token embeddings
    params += (long long)c.vocab_size * c.d_model;
    // Position embeddings
    params += (long long)c.max_seq_len * c.d_model;
    // Transformer layers
    long long per_layer = 0;
    per_layer += 4LL * c.d_model * c.d_model;  // Q, K, V, O projections
    per_layer += 4LL * c.d_model;               // Q, K, V, O biases
    per_layer += 2LL * c.d_model;               // LayerNorm1 gamma, beta
    per_layer += (long long)c.d_model * c.d_ff; // FFN W1
    per_layer += c.d_ff;                         // FFN b1
    per_layer += (long long)c.d_ff * c.d_model; // FFN W2
    per_layer += c.d_model;                      // FFN b2
    per_layer += 2LL * c.d_model;               // LayerNorm2 gamma, beta
    params += per_layer * c.num_layers;
    // Final layer norm
    params += 2LL * c.d_model;
    // LM head (weight tied with embeddings, so no additional params)
    return params;
}

} // namespace llm
