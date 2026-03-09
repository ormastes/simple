/**
 * @file expert_config.h
 * @brief Configuration for Mixture of Experts (MoE) with dynamic loading
 */

#pragma once

#include <cstdint>
#include <cstddef>

namespace attention_expert {

/**
 * @brief Configuration for Mixture of Experts layer
 */
struct ExpertConfig {
    size_t num_experts;         ///< Total number of experts
    size_t experts_per_token;   ///< Top-K experts activated per token
    size_t hidden_dim;          ///< Hidden dimension
    size_t ffn_dim;             ///< Feed-forward intermediate dimension
    bool use_bias;              ///< Whether to use bias in expert layers
    float capacity_factor;      ///< Load balancing capacity factor
    bool normalize_scores;      ///< Whether to normalize routing scores

    ExpertConfig() :
        num_experts(8),
        experts_per_token(2),
        hidden_dim(512),
        ffn_dim(2048),
        use_bias(true),
        capacity_factor(1.25f),
        normalize_scores(true) {}
};

/**
 * @brief Single expert weights (feed-forward network)
 */
struct ExpertWeights {
    float* w1;                  ///< First linear layer [ffn_dim, hidden_dim]
    float* w2;                  ///< Second linear layer [hidden_dim, ffn_dim]
    float* b1;                  ///< First layer bias [ffn_dim] (optional)
    float* b2;                  ///< Second layer bias [hidden_dim] (optional)

    ExpertWeights() : w1(nullptr), w2(nullptr), b1(nullptr), b2(nullptr) {}
};

/**
 * @brief Expert routing information
 */
struct RoutingInfo {
    int* expert_indices;        ///< Expert IDs per token [batch*seq_len, top_k]
    float* routing_weights;     ///< Routing probabilities [batch*seq_len, top_k]
    int* expert_capacity;       ///< Per-expert token count [num_experts]

    RoutingInfo() :
        expert_indices(nullptr),
        routing_weights(nullptr),
        expert_capacity(nullptr) {}
};

/**
 * @brief NVMe storage layout for expert weights
 */
struct ExpertNVMeLayout {
    uint64_t base_offset;       ///< Base offset in NVMe device (bytes)
    size_t expert_size_bytes;   ///< Size of single expert weights
    size_t stride_bytes;        ///< Stride between experts (for alignment)

    /**
     * @brief Get NVMe offset for specific expert
     * @param expert_id Expert index (0-based)
     * @return Byte offset in NVMe device
     */
    uint64_t get_expert_offset(size_t expert_id) const {
        return base_offset + expert_id * stride_bytes;
    }

    ExpertNVMeLayout() :
        base_offset(0),
        expert_size_bytes(0),
        stride_bytes(0) {}
};

/**
 * @brief Dynamic expert loading configuration
 */
struct ExpertLoadConfig {
    bool load_on_demand;            ///< Enable dynamic loading from NVMe
    const char* nvme_device_path;   ///< NVMe device path
    ExpertNVMeLayout layout;        ///< Storage layout
    void** expert_cache_ptrs;       ///< Per-expert GPU cache pointers [num_experts]
    bool* expert_loaded;            ///< Per-expert loaded status [num_experts]
    size_t max_cached_experts;      ///< Maximum experts to keep in GPU memory
    void* io_buffer;                ///< Pre-allocated I/O buffer (pinned memory)
    size_t io_buffer_size;          ///< I/O buffer size in bytes

    ExpertLoadConfig() :
        load_on_demand(false),
        nvme_device_path(nullptr),
        expert_cache_ptrs(nullptr),
        expert_loaded(nullptr),
        max_cached_experts(0),
        io_buffer(nullptr),
        io_buffer_size(0) {}
};

/**
 * @brief MoE forward pass output
 */
struct MoEOutput {
    float* output;                  ///< Output tensor [batch, seq_len, hidden_dim]
    RoutingInfo routing;            ///< Routing information (for backward pass)
    float* load_balancing_loss;     ///< Load balancing auxiliary loss (optional)

    MoEOutput() : output(nullptr), load_balancing_loss(nullptr) {}
};

/**
 * @brief MoE backward pass gradients
 */
struct MoEGradients {
    float* grad_input;              ///< Gradient w.r.t. input
    ExpertWeights* grad_experts;    ///< Per-expert weight gradients [num_experts]
    float* grad_router;             ///< Gradient w.r.t. router weights

    MoEGradients() :
        grad_input(nullptr),
        grad_experts(nullptr),
        grad_router(nullptr) {}
};

/**
 * @brief Expert activation strategy
 */
enum class ExpertActivation {
    GELU,                   ///< Gaussian Error Linear Unit
    RELU,                   ///< Rectified Linear Unit
    SILU,                   ///< Sigmoid Linear Unit (Swish)
    GEGLU                   ///< GELU with gating
};

} // namespace attention_expert
