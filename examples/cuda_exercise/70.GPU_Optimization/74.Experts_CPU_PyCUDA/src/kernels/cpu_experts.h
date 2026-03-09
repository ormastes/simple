/**
 * @file cpu_experts.h
 * @brief CPU Mixture of Experts (MoE) header
 *
 * Declares CPU-based MoE functions including gating/routing,
 * expert FFN computation, full MoE forward pass, and GELU activation.
 * Uses flat buffer layout for expert weights to enable simple ctypes bindings.
 */

#pragma once

#include <chrono>
#include <cstring>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Gating/Router: compute top-k expert selection with softmax weights
 *
 * For each token in the batch, computes softmax over gate_logits and selects
 * the top_k experts with highest probabilities.
 *
 * @param[out] expert_indices  Selected expert indices [batch_size * top_k]
 * @param[out] expert_weights  Softmax weights for selected experts [batch_size * top_k]
 * @param[in]  gate_logits     Raw gate logits [batch_size * num_experts]
 * @param[in]  batch_size      Number of tokens in the batch
 * @param[in]  num_experts     Total number of experts
 * @param[in]  top_k           Number of experts to select per token
 */
void cpu_topk_gating(int* expert_indices, float* expert_weights,
                    const float* gate_logits, int batch_size, int num_experts, int top_k);

/**
 * @brief Single expert FFN: output = GELU(input * W1 + b1) * W2 + b2
 *
 * Computes a two-layer feed-forward network with GELU activation for a single expert.
 * Uses flat buffer layout: weights_1[num_experts * d_ff * d_model], etc.
 * The expert_idx parameter selects which expert's weights to use from the flat buffer.
 *
 * @param[out] output       Output tensor [batch_size * d_model]
 * @param[in]  input        Input tensor [batch_size * d_model]
 * @param[in]  weights_1    All expert W1 weights [num_experts * d_ff * d_model]
 * @param[in]  bias_1       All expert b1 biases [num_experts * d_ff]
 * @param[in]  weights_2    All expert W2 weights [num_experts * d_model * d_ff]
 * @param[in]  bias_2       All expert b2 biases [num_experts * d_model]
 * @param[in]  batch_size   Number of tokens
 * @param[in]  d_model      Model dimension
 * @param[in]  d_ff         Feed-forward hidden dimension
 * @param[in]  expert_idx   Index of the expert to use
 * @param[in]  num_experts  Total number of experts (for computing offsets)
 */
void cpu_expert_ffn(float* output, const float* input,
                   const float* weights_1, const float* bias_1,
                   const float* weights_2, const float* bias_2,
                   int batch_size, int d_model, int d_ff, int expert_idx, int num_experts);

/**
 * @brief Full MoE forward: route tokens to experts, compute, combine
 *
 * Implements the complete Mixture of Experts forward pass:
 * 1. Compute gate logits from input and gate_weights
 * 2. Select top_k experts per token via softmax + top-k
 * 3. Compute expert FFN outputs for selected experts
 * 4. Weighted sum of expert outputs
 *
 * @param[out] output            Output tensor [batch_size * d_model]
 * @param[in]  input             Input tensor [batch_size * d_model]
 * @param[in]  gate_weights      Gating network weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All expert W1 [num_experts * d_ff * d_model]
 * @param[in]  expert_bias_1     All expert b1 [num_experts * d_ff]
 * @param[in]  expert_weights_2  All expert W2 [num_experts * d_model * d_ff]
 * @param[in]  expert_bias_2     All expert b2 [num_experts * d_model]
 * @param[in]  batch_size        Number of tokens
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Feed-forward hidden dimension
 * @param[in]  num_experts       Total number of experts
 * @param[in]  top_k             Number of experts per token
 */
void cpu_moe_forward(float* output, const float* input,
                    const float* gate_weights,
                    const float* expert_weights_1, const float* expert_bias_1,
                    const float* expert_weights_2, const float* expert_bias_2,
                    int batch_size, int d_model, int d_ff, int num_experts, int top_k);

/**
 * @brief GELU activation function
 *
 * Computes GELU(x) = x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 *
 * @param[out] output  Output tensor [n]
 * @param[in]  input   Input tensor [n]
 * @param[in]  n       Number of elements
 */
void cpu_gelu(float* output, const float* input, int n);

/**
 * @brief Parallel MoE forward using OpenMP
 *
 * Same as cpu_moe_forward but parallelized over the batch dimension using OpenMP.
 *
 * @param[out] output            Output tensor [batch_size * d_model]
 * @param[in]  input             Input tensor [batch_size * d_model]
 * @param[in]  gate_weights      Gating network weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All expert W1 [num_experts * d_ff * d_model]
 * @param[in]  expert_bias_1     All expert b1 [num_experts * d_ff]
 * @param[in]  expert_weights_2  All expert W2 [num_experts * d_model * d_ff]
 * @param[in]  expert_bias_2     All expert b2 [num_experts * d_model]
 * @param[in]  batch_size        Number of tokens
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Feed-forward hidden dimension
 * @param[in]  num_experts       Total number of experts
 * @param[in]  top_k             Number of experts per token
 * @param[in]  num_threads       Number of OpenMP threads (-1 for all available)
 */
void cpu_moe_forward_parallel(float* output, const float* input,
                             const float* gate_weights,
                             const float* expert_weights_1, const float* expert_bias_1,
                             const float* expert_weights_2, const float* expert_bias_2,
                             int batch_size, int d_model, int d_ff, int num_experts, int top_k,
                             int num_threads);

/**
 * @brief Timed MoE forward pass
 *
 * Runs the MoE forward pass and returns elapsed time in milliseconds.
 * Selects between "naive", "parallel" methods via the method string.
 *
 * @param[out] output            Output tensor [batch_size * d_model]
 * @param[in]  input             Input tensor [batch_size * d_model]
 * @param[in]  gate_weights      Gating network weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All expert W1 [num_experts * d_ff * d_model]
 * @param[in]  expert_bias_1     All expert b1 [num_experts * d_ff]
 * @param[in]  expert_weights_2  All expert W2 [num_experts * d_model * d_ff]
 * @param[in]  expert_bias_2     All expert b2 [num_experts * d_model]
 * @param[in]  batch_size        Number of tokens
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Feed-forward hidden dimension
 * @param[in]  num_experts       Total number of experts
 * @param[in]  top_k             Number of experts per token
 * @param[in]  method            Method name: "naive" or "parallel"
 * @return     Elapsed time in milliseconds
 */
float cpu_moe_timed(float* output, const float* input,
                   const float* gate_weights,
                   const float* expert_weights_1, const float* expert_bias_1,
                   const float* expert_weights_2, const float* expert_bias_2,
                   int batch_size, int d_model, int d_ff, int num_experts, int top_k,
                   const char* method);

#ifdef __cplusplus
}
#endif
