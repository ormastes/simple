/**
 * @file moe_layer.h
 * @brief Complete MoE layer combining router, dispatch, experts, and combine
 *
 * Orchestrates the full Mixture-of-Experts computation pipeline:
 * 1. Route tokens to experts via top-k gating
 * 2. Dispatch tokens to their selected experts
 * 3. Run each expert's FFN on its assigned tokens
 * 4. Combine expert outputs with routing weights
 */

#pragma once

#include <cuda_runtime.h>
#include "expert_network.h"
#include "topk_router.h"

namespace llm {

/**
 * @brief MoE layer configuration combining router and expert settings
 *
 * Holds all parameters needed to instantiate and run a complete MoE layer.
 */
struct MoELayerConfig {
    RouterConfig router;      ///< Router configuration
    int d_model;              ///< Model hidden dimension
    int d_ff;                 ///< FFN intermediate dimension
    float aux_loss_weight;    ///< Weight for load balancing auxiliary loss

    /**
     * @brief Construct MoE layer configuration
     *
     * @param num_experts   Number of expert networks
     * @param top_k         Experts selected per token
     * @param d_model       Model hidden dimension
     * @param d_ff          FFN intermediate dimension
     * @param aux_loss_weight Auxiliary loss weight (default: 0.01)
     */
    MoELayerConfig(int num_experts = 8, int top_k = 2,
                   int d_model = 64, int d_ff = 256,
                   float aux_loss_weight = 0.01f)
        : router(num_experts, top_k, d_model),
          d_model(d_model), d_ff(d_ff),
          aux_loss_weight(aux_loss_weight) {}
};

/**
 * @brief Complete MoE layer forward pass
 *
 * Executes the full MoE pipeline:
 * 1. Compute routing probabilities and select top-k experts per token
 * 2. Dispatch each token to its selected experts (scatter)
 * 3. Run expert FFNs on their assigned tokens
 * 4. Combine expert outputs weighted by routing probabilities (gather)
 *
 * @param[out] output         Output tensor [num_tokens, d_model]
 * @param[in]  input          Input tensor [num_tokens, d_model]
 * @param[in]  W_router       Router gate weights [num_experts, d_model]
 * @param[in]  experts        Expert network weights
 * @param[in]  config         MoE layer configuration
 * @param[in]  num_tokens     Total number of tokens (batch_size * seq_len)
 * @param[out] aux_loss       Auxiliary load balancing loss (scalar, device ptr)
 * @param[in]  stream         CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @note aux_loss can be nullptr if load balancing loss is not needed
 */
void moe_layer_forward(float* output, const float* input,
                       const float* W_router,
                       const ExpertWeights& experts,
                       const MoELayerConfig& config,
                       int num_tokens,
                       float* aux_loss = nullptr,
                       cudaStream_t stream = 0);

} // namespace llm
