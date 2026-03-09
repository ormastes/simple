/**
 * @file expert_network.h
 * @brief Expert network interface for MoE layers
 *
 * Defines the weight structure and forward pass for individual expert networks.
 * Each expert is a SwiGLU FFN with its own set of gate, up, and down projection
 * weights, sharing the same architecture as the dense FFN in Module 67.
 */

#pragma once

#include <cuda_runtime.h>
#include "common/swiglu_ffn.h"
#include "common/deepseek_config.h"

namespace llm {

/**
 * @brief Weights for all experts in one MoE layer
 *
 * Stores weight matrices for num_experts expert networks. Each expert has
 * the same SwiGLU architecture (W_gate, W_up, W_down) but independent weights.
 */
struct ExpertWeights {
    int num_experts;   ///< Number of experts
    int d_model;       ///< Model hidden dimension
    int d_ff;          ///< Feed-forward intermediate dimension

    /// Expert weight arrays: each element is one expert's SwiGLU weights.
    /// Index [expert_id] for each array.
    float** W_gate;    ///< Gate projections [num_experts][d_model * d_ff]
    float** W_up;      ///< Up projections [num_experts][d_model * d_ff]
    float** W_down;    ///< Down projections [num_experts][d_ff * d_model]
};

/**
 * @brief Run a single expert's SwiGLU FFN on its assigned tokens
 *
 * Applies the SwiGLU computation for one expert to a subset of tokens
 * that the router has assigned to it.
 *
 * @param[out] output       Output [num_tokens, d_model]
 * @param[in]  input        Input tokens assigned to this expert [num_tokens, d_model]
 * @param[in]  W_gate       Gate weight [d_ff, d_model]
 * @param[in]  W_up         Up weight [d_ff, d_model]
 * @param[in]  W_down       Down weight [d_model, d_ff]
 * @param[in]  d_model      Model dimension
 * @param[in]  d_ff         FFN intermediate dimension
 * @param[in]  num_tokens   Number of tokens assigned to this expert
 * @param[in]  stream       CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 */
void expert_forward(float* output, const float* input,
                    const float* W_gate, const float* W_up, const float* W_down,
                    int d_model, int d_ff, int num_tokens,
                    cudaStream_t stream = 0);

/**
 * @brief Allocate weights for all experts
 *
 * @param[in] num_experts Number of expert networks
 * @param[in] d_model     Model hidden dimension
 * @param[in] d_ff        FFN intermediate dimension
 * @return ExpertWeights with allocated device pointers
 *
 * @note Caller must call free_expert_weights() to release memory
 */
ExpertWeights allocate_expert_weights(int num_experts, int d_model, int d_ff);

/**
 * @brief Free all expert weights
 *
 * @param[in,out] weights Weights to free; all pointers set to nullptr
 */
void free_expert_weights(ExpertWeights& weights);

/**
 * @brief Initialize all expert weights with Xavier initialization
 *
 * @param[in,out] weights Pre-allocated expert weights
 * @param[in]     seed    Random seed (default: 42)
 */
void initialize_expert_weights(ExpertWeights& weights, unsigned int seed = 42);

} // namespace llm
