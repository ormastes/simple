/**
 * @file attention_types.h
 * @brief Data structures and types for attention mechanisms
 */

#pragma once

#include <cstdint>
#include <cstddef>

namespace attention_expert {

/**
 * @brief Configuration for multi-head attention
 */
struct AttentionConfig {
    size_t batch_size;      ///< Batch size
    size_t seq_len;         ///< Sequence length
    size_t num_heads;       ///< Number of attention heads
    size_t head_dim;        ///< Dimension per head
    size_t hidden_dim;      ///< Hidden dimension (num_heads * head_dim)
    bool use_bias;          ///< Whether to use bias in linear projections
    float dropout;          ///< Dropout probability (0.0 = no dropout)
    bool causal;            ///< Whether to use causal (autoregressive) mask
};

/**
 * @brief Weight tensor dimensions for attention
 */
struct AttentionWeights {
    float* q_weight;        ///< Query projection weight [hidden_dim, hidden_dim]
    float* k_weight;        ///< Key projection weight [hidden_dim, hidden_dim]
    float* v_weight;        ///< Value projection weight [hidden_dim, hidden_dim]
    float* o_weight;        ///< Output projection weight [hidden_dim, hidden_dim]

    float* q_bias;          ///< Query bias [hidden_dim] (optional)
    float* k_bias;          ///< Key bias [hidden_dim] (optional)
    float* v_bias;          ///< Value bias [hidden_dim] (optional)
    float* o_bias;          ///< Output bias [hidden_dim] (optional)

    AttentionWeights() :
        q_weight(nullptr), k_weight(nullptr), v_weight(nullptr), o_weight(nullptr),
        q_bias(nullptr), k_bias(nullptr), v_bias(nullptr), o_bias(nullptr) {}
};

/**
 * @brief Loading mode for attention weights
 */
enum class LoadMode {
    ALL_IN_MEMORY,          ///< All weights pre-loaded in GPU memory
    DYNAMIC_FFN_ONLY,       ///< Load only feed-forward weights on-demand
    DYNAMIC_ALL             ///< Load all weights (QKV + FFN) on-demand
};

/**
 * @brief NVMe loading configuration for dynamic weight loading
 */
struct NVMeLoadConfig {
    LoadMode mode;              ///< Loading strategy
    const char* nvme_path;      ///< Path to NVMe device or file
    uint64_t weight_offset;     ///< Byte offset in NVMe device
    size_t weight_size_bytes;   ///< Total size of weights in bytes
    void* staging_buffer;       ///< Pre-allocated staging buffer (GPU memory)
    bool use_pinned_memory;     ///< Whether to use pinned host memory

    NVMeLoadConfig() :
        mode(LoadMode::ALL_IN_MEMORY),
        nvme_path(nullptr),
        weight_offset(0),
        weight_size_bytes(0),
        staging_buffer(nullptr),
        use_pinned_memory(true) {}
};

/**
 * @brief Attention forward pass output
 */
struct AttentionOutput {
    float* output;              ///< Output tensor [batch, seq_len, hidden_dim]
    float* attention_scores;    ///< Attention weights [batch, heads, seq_len, seq_len] (optional)

    AttentionOutput() : output(nullptr), attention_scores(nullptr) {}
};

/**
 * @brief Attention backward pass gradients
 */
struct AttentionGradients {
    float* grad_input;          ///< Gradient w.r.t. input
    float* grad_q_weight;       ///< Gradient w.r.t. query weight
    float* grad_k_weight;       ///< Gradient w.r.t. key weight
    float* grad_v_weight;       ///< Gradient w.r.t. value weight
    float* grad_o_weight;       ///< Gradient w.r.t. output weight
    float* grad_q_bias;         ///< Gradient w.r.t. query bias
    float* grad_k_bias;         ///< Gradient w.r.t. key bias
    float* grad_v_bias;         ///< Gradient w.r.t. value bias
    float* grad_o_bias;         ///< Gradient w.r.t. output bias

    AttentionGradients() :
        grad_input(nullptr), grad_q_weight(nullptr), grad_k_weight(nullptr),
        grad_v_weight(nullptr), grad_o_weight(nullptr),
        grad_q_bias(nullptr), grad_k_bias(nullptr), grad_v_bias(nullptr),
        grad_o_bias(nullptr) {}
};

} // namespace attention_expert
