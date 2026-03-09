/**
 * @file router_kernels.cu
 * @brief CUDA kernels for MoE top-k expert routing
 *
 * Implements the gating mechanism that decides which experts process each token.
 * The router performs three steps:
 * 1. Compute gate logits via matrix multiplication: gate = input * W_gate^T
 * 2. Apply softmax to obtain routing probabilities
 * 3. Select top-k experts per token and renormalize weights
 */

#include "common/topk_router.h"
#include "cuda_utils.h"
#include <cmath>
#include <vector>

namespace llm {

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Compute gate logits: gate[i][j] = dot(input[i], W_gate[j])
 *
 * Each token's hidden state is projected to num_experts dimensions.
 *
 * @param[out] gate       Gate logits [num_tokens, num_experts]
 * @param[in]  input      Input tokens [num_tokens, d_model]
 * @param[in]  W_gate     Gate weights [num_experts, d_model]
 * @param[in]  num_tokens Number of tokens
 * @param[in]  d_model    Model dimension
 * @param[in]  num_experts Number of experts
 */
__global__ void router_gate_kernel(
    float* gate, const float* input, const float* W_gate,
    int num_tokens, int d_model, int num_experts
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int expert_idx = blockIdx.y * blockDim.y + threadIdx.y;

    if (token_idx < num_tokens && expert_idx < num_experts) {
        float sum = 0.0f;
        for (int k = 0; k < d_model; k++) {
            sum += input[token_idx * d_model + k] * W_gate[expert_idx * d_model + k];
        }
        gate[token_idx * num_experts + expert_idx] = sum;
    }
}

/**
 * @brief Softmax over the expert dimension for each token
 *
 * Computes softmax in-place: gate[i][j] = exp(gate[i][j]) / sum_j exp(gate[i][j])
 *
 * @param[in,out] gate        Gate logits/probabilities [num_tokens, num_experts]
 * @param[in]     num_tokens  Number of tokens
 * @param[in]     num_experts Number of experts
 */
__global__ void router_softmax_kernel(
    float* gate, int num_tokens, int num_experts
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (token_idx >= num_tokens) return;

    float* row = gate + token_idx * num_experts;

    // Find max for numerical stability
    float max_val = row[0];
    for (int j = 1; j < num_experts; j++) {
        if (row[j] > max_val) max_val = row[j];
    }

    // Compute exp and sum
    float sum = 0.0f;
    for (int j = 0; j < num_experts; j++) {
        row[j] = expf(row[j] - max_val);
        sum += row[j];
    }

    // Normalize
    float inv_sum = 1.0f / (sum + 1e-8f);
    for (int j = 0; j < num_experts; j++) {
        row[j] *= inv_sum;
    }
}

/**
 * @brief Top-k selection and renormalization per token
 *
 * For each token, finds the top-k experts with highest routing probabilities,
 * stores their indices, and renormalizes the selected weights to sum to 1.
 *
 * @param[in]  gate_probs     Softmax routing probabilities [num_tokens, num_experts]
 * @param[out] expert_indices Selected expert IDs [num_tokens, top_k]
 * @param[out] expert_weights Renormalized routing weights [num_tokens, top_k]
 * @param[in]  num_tokens     Number of tokens
 * @param[in]  num_experts    Number of experts
 * @param[in]  top_k          Number of experts to select per token
 */
__global__ void router_topk_kernel(
    const float* gate_probs, int* expert_indices, float* expert_weights,
    int num_tokens, int num_experts, int top_k
) {
    int token_idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (token_idx >= num_tokens) return;

    const float* probs = gate_probs + token_idx * num_experts;
    int* out_indices = expert_indices + token_idx * top_k;
    float* out_weights = expert_weights + token_idx * top_k;

    // Simple top-k selection via repeated max finding
    // (Efficient for small num_experts, typical in MoE: 8-64)
    bool selected[256] = {}; // Assumes num_experts <= 256

    for (int k = 0; k < top_k; k++) {
        float best_val = -1e30f;
        int best_idx = 0;

        for (int j = 0; j < num_experts; j++) {
            if (!selected[j] && probs[j] > best_val) {
                best_val = probs[j];
                best_idx = j;
            }
        }

        selected[best_idx] = true;
        out_indices[k] = best_idx;
        out_weights[k] = best_val;
    }

    // Renormalize selected weights to sum to 1
    float weight_sum = 0.0f;
    for (int k = 0; k < top_k; k++) {
        weight_sum += out_weights[k];
    }

    float inv_sum = 1.0f / (weight_sum + 1e-8f);
    for (int k = 0; k < top_k; k++) {
        out_weights[k] *= inv_sum;
    }
}

// ============================================================================
// Launch wrappers
// ============================================================================

void topk_route(RouterOutput& output, const float* input,
                const float* W_gate,
                const RouterConfig& config,
                int num_tokens,
                cudaStream_t stream) {
    int num_experts = config.num_experts;
    int d_model = config.d_model;
    int top_k = config.top_k;

    output.num_tokens = num_tokens;

    // Step 1: Compute gate logits
    dim3 gate_block(16, 16);
    dim3 gate_grid((num_tokens + 15) / 16, (num_experts + 15) / 16);
    router_gate_kernel<<<gate_grid, gate_block, 0, stream>>>(
        output.gate_logits, input, W_gate, num_tokens, d_model, num_experts);

    // Step 2: Softmax
    int sm_threads = 256;
    int sm_blocks = (num_tokens + sm_threads - 1) / sm_threads;
    router_softmax_kernel<<<sm_blocks, sm_threads, 0, stream>>>(
        output.gate_logits, num_tokens, num_experts);

    // Step 3: Top-k selection
    int tk_threads = 256;
    int tk_blocks = (num_tokens + tk_threads - 1) / tk_threads;
    router_topk_kernel<<<tk_blocks, tk_threads, 0, stream>>>(
        output.gate_logits, output.expert_indices, output.expert_weights,
        num_tokens, num_experts, top_k);

    CHECK_CUDA(cudaStreamSynchronize(stream));
}

RouterOutput allocate_router_output(int num_tokens, const RouterConfig& config) {
    RouterOutput output = {};
    output.num_tokens = num_tokens;

    CHECK_CUDA(cudaMalloc(&output.expert_indices,
                          num_tokens * config.top_k * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&output.expert_weights,
                          num_tokens * config.top_k * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&output.gate_logits,
                          num_tokens * config.num_experts * sizeof(float)));

    return output;
}

void free_router_output(RouterOutput& output) {
    if (output.expert_indices) { cudaFree(output.expert_indices); output.expert_indices = nullptr; }
    if (output.expert_weights) { cudaFree(output.expert_weights); output.expert_weights = nullptr; }
    if (output.gate_logits) { cudaFree(output.gate_logits); output.gate_logits = nullptr; }
}

} // namespace llm
