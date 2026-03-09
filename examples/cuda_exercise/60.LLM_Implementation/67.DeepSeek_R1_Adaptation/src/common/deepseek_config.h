/**
 * @file deepseek_config.h
 * @brief DeepSeek R1 model configuration
 *
 * Defines the hyperparameters for the DeepSeek R1 model family, including
 * GQA head counts, RoPE theta, MoE expert counts, and SwiGLU dimensions.
 * Provides preset configurations for different model sizes.
 */

#pragma once

namespace llm {

/**
 * @brief Configuration for a DeepSeek R1 model
 *
 * Holds all architectural hyperparameters needed to instantiate a DeepSeek R1
 * model or any of its sub-components (GQA, RoPE, SwiGLU, MoE).
 */
struct DeepSeekConfig {
    int vocab_size;       ///< Vocabulary size
    int d_model;          ///< Model hidden dimension
    int num_heads;        ///< Number of query heads
    int num_kv_heads;     ///< Number of KV heads (GQA: fewer than query heads)
    int num_layers;       ///< Number of transformer layers
    int d_ff;             ///< Feed-forward intermediate dimension
    int max_seq_len;      ///< Maximum sequence length
    float rope_theta;     ///< RoPE base frequency
    int num_experts;      ///< Number of MoE experts (0 = dense, no MoE)
    int top_k_experts;    ///< Top-k expert selection for MoE routing

    /**
     * @brief Default constructor with DeepSeek R1 7B-like defaults
     */
    DeepSeekConfig()
        : vocab_size(102400), d_model(4096), num_heads(32),
          num_kv_heads(8), num_layers(30), d_ff(11008),
          max_seq_len(4096), rope_theta(10000.0f),
          num_experts(0), top_k_experts(2) {}
};

/**
 * @brief DeepSeek R1 7B configuration (simplified)
 *
 * Returns a configuration matching the DeepSeek R1 7B model architecture
 * with 32 query heads, 8 KV heads, and 4096-dimensional hidden state.
 *
 * @return DeepSeekConfig for the 7B model
 */
inline DeepSeekConfig deepseek_7b() {
    DeepSeekConfig c;
    c.vocab_size = 102400;
    c.d_model = 4096;
    c.num_heads = 32;
    c.num_kv_heads = 8;
    c.num_layers = 30;
    c.d_ff = 11008;
    c.max_seq_len = 4096;
    c.rope_theta = 10000.0f;
    return c;
}

/**
 * @brief Tiny configuration for unit testing
 *
 * Returns a minimal configuration suitable for fast unit tests with
 * small dimensions that still exercise all code paths (GQA grouping, etc.).
 *
 * @return DeepSeekConfig with tiny dimensions
 */
inline DeepSeekConfig deepseek_tiny() {
    DeepSeekConfig c;
    c.vocab_size = 256;
    c.d_model = 64;
    c.num_heads = 8;
    c.num_kv_heads = 2;
    c.num_layers = 2;
    c.d_ff = 256;
    c.max_seq_len = 128;
    c.rope_theta = 10000.0f;
    return c;
}

} // namespace llm
