/**
 * @file topk_router.h
 * @brief Top-K expert router interface for MoE layers
 *
 * Implements the gating mechanism that decides which experts process each token.
 * The router computes a softmax over expert scores and selects the top-k experts
 * for each token. An auxiliary load balancing loss encourages uniform expert usage.
 */

#pragma once

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Router configuration
 *
 * Controls the gating network and expert selection behavior.
 */
struct RouterConfig {
    int num_experts;       ///< Total number of available experts
    int top_k;             ///< Number of experts selected per token
    int d_model;           ///< Model hidden dimension (input to router)
    float jitter_noise;    ///< Multiplicative jitter for load balancing (0.0 = none)
    float capacity_factor; ///< Expert capacity factor (1.0 = no overflow)

    /**
     * @brief Construct router configuration
     *
     * @param num_experts   Total expert count
     * @param top_k         Experts per token
     * @param d_model       Input dimension
     * @param jitter_noise  Noise for load balancing (default: 0.0)
     * @param capacity_factor Expert capacity multiplier (default: 1.25)
     */
    RouterConfig(int num_experts = 8, int top_k = 2, int d_model = 64,
                 float jitter_noise = 0.0f, float capacity_factor = 1.25f)
        : num_experts(num_experts), top_k(top_k), d_model(d_model),
          jitter_noise(jitter_noise), capacity_factor(capacity_factor) {}
};

/**
 * @brief Router output: selected experts and their weights per token
 *
 * Contains the routing decisions made by the gating network.
 */
struct RouterOutput {
    int* expert_indices;     ///< Selected expert IDs [num_tokens, top_k]
    float* expert_weights;   ///< Normalized routing weights [num_tokens, top_k]
    float* gate_logits;      ///< Raw gate logits [num_tokens, num_experts]
    int num_tokens;          ///< Total number of tokens routed
};

/**
 * @brief Compute top-k expert routing
 *
 * For each token:
 * 1. Compute gate logits: gate = input * W_gate^T  [num_tokens, num_experts]
 * 2. Apply softmax to get routing probabilities
 * 3. Select top-k experts per token
 * 4. Renormalize selected expert weights to sum to 1
 *
 * @param[out] output     Router output with expert indices and weights
 * @param[in]  input      Input tokens [num_tokens, d_model]
 * @param[in]  W_gate     Gate weight matrix [num_experts, d_model]
 * @param[in]  config     Router configuration
 * @param[in]  num_tokens Total number of tokens
 * @param[in]  stream     CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 */
void topk_route(RouterOutput& output, const float* input,
                const float* W_gate,
                const RouterConfig& config,
                int num_tokens,
                cudaStream_t stream = 0);

/**
 * @brief Allocate router output buffers
 *
 * @param[in] num_tokens  Number of tokens to route
 * @param[in] config      Router configuration
 * @return RouterOutput with allocated device pointers
 */
RouterOutput allocate_router_output(int num_tokens, const RouterConfig& config);

/**
 * @brief Free router output buffers
 *
 * @param[in,out] output Router output to free
 */
void free_router_output(RouterOutput& output);

} // namespace llm
