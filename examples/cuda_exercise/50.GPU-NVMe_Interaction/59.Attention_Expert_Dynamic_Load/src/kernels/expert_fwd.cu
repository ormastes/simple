/**
 * @file expert_fwd.cu
 * @brief CUDA kernels for Mixture of Experts forward pass with dynamic loading
 */

#include "expert_config.h"
#include "cuda_utils.h"
#include <cuda_runtime.h>

namespace attention_expert {

/**
 * @brief Router network - compute expert routing scores
 *
 * @param[in]  input           Input [batch*seq_len, hidden_dim]
 * @param[in]  router_weight   Router weights [num_experts, hidden_dim]
 * @param[out] routing_scores  Output scores [batch*seq_len, num_experts]
 * @param[in]  tokens          Number of tokens
 * @param[in]  hidden_dim      Hidden dimension
 * @param[in]  num_experts     Number of experts
 */
__global__ void compute_routing_scores_kernel(
    const float* __restrict__ input,
    const float* __restrict__ router_weight,
    float* __restrict__ routing_scores,
    int tokens,
    int hidden_dim,
    int num_experts
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int expert_idx = blockIdx.y;

    if (token_idx < tokens && expert_idx < num_experts) {
        float score = 0.0f;
        for (int d = 0; d < hidden_dim; ++d) {
            score += input[token_idx * hidden_dim + d] *
                     router_weight[expert_idx * hidden_dim + d];
        }
        routing_scores[token_idx * num_experts + expert_idx] = score;
    }
}

/**
 * @brief Top-K expert selection per token
 */
__global__ void select_top_k_experts_kernel(
    const float* __restrict__ routing_scores,
    int* __restrict__ expert_indices,
    float* __restrict__ routing_weights,
    int tokens,
    int num_experts,
    int k
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (token_idx >= tokens) return;

    // Simple top-k selection (can be optimized with shared memory sort)
    const float* scores = routing_scores + token_idx * num_experts;

    for (int i = 0; i < k; ++i) {
        int best_idx = 0;
        float best_score = -1e9f;

        for (int e = 0; e < num_experts; ++e) {
            bool already_selected = false;
            for (int j = 0; j < i; ++j) {
                if (expert_indices[token_idx * k + j] == e) {
                    already_selected = true;
                    break;
                }
            }

            if (!already_selected && scores[e] > best_score) {
                best_score = scores[e];
                best_idx = e;
            }
        }

        expert_indices[token_idx * k + i] = best_idx;
        routing_weights[token_idx * k + i] = best_score;
    }

    // Normalize routing weights (softmax over top-k)
    float sum = 0.0f;
    for (int i = 0; i < k; ++i) {
        routing_weights[token_idx * k + i] = expf(routing_weights[token_idx * k + i]);
        sum += routing_weights[token_idx * k + i];
    }
    for (int i = 0; i < k; ++i) {
        routing_weights[token_idx * k + i] /= sum;
    }
}

/**
 * @brief Expert FFN forward pass
 *
 * Computes: output = GELU(input * w1) * w2
 */
__global__ void expert_ffn_kernel(
    const float* __restrict__ input,
    const float* __restrict__ w1,
    const float* __restrict__ w2,
    const float* __restrict__ b1,
    const float* __restrict__ b2,
    float* __restrict__ output,
    int num_tokens,
    int hidden_dim,
    int ffn_dim
) {
    int token_idx = blockIdx.x;
    int h_idx = threadIdx.x;

    if (token_idx >= num_tokens || h_idx >= hidden_dim) return;

    __shared__ float intermediate[2048]; // Max ffn_dim

    // First layer: hidden -> ffn_dim with GELU
    if (h_idx < ffn_dim) {
        float sum = b1 ? b1[h_idx] : 0.0f;
        for (int d = 0; d < hidden_dim; ++d) {
            sum += input[token_idx * hidden_dim + d] * w1[h_idx * hidden_dim + d];
        }

        // GELU activation: 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
        float x = sum;
        float x3 = x * x * x;
        intermediate[h_idx] = 0.5f * x * (1.0f + tanhf(0.797885f * (x + 0.044715f * x3)));
    }
    __syncthreads();

    // Second layer: ffn_dim -> hidden
    if (h_idx < hidden_dim) {
        float sum = b2 ? b2[h_idx] : 0.0f;
        for (int f = 0; f < ffn_dim; ++f) {
            sum += intermediate[f] * w2[h_idx * ffn_dim + f];
        }
        output[token_idx * hidden_dim + h_idx] = sum;
    }
}

/**
 * @brief Combine expert outputs with routing weights
 */
__global__ void combine_expert_outputs_kernel(
    const float* __restrict__ expert_outputs,
    const float* __restrict__ routing_weights,
    const int* __restrict__ expert_indices,
    float* __restrict__ output,
    int tokens,
    int hidden_dim,
    int k
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int dim_idx = blockIdx.y * blockDim.y + threadIdx.y;

    if (token_idx < tokens && dim_idx < hidden_dim) {
        float sum = 0.0f;
        for (int i = 0; i < k; ++i) {
            int expert_output_idx = (token_idx * k + i) * hidden_dim + dim_idx;
            float weight = routing_weights[token_idx * k + i];
            sum += weight * expert_outputs[expert_output_idx];
        }
        output[token_idx * hidden_dim + dim_idx] = sum;
    }
}

} // namespace attention_expert
