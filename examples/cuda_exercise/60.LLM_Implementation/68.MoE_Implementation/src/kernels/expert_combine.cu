/**
 * @file expert_combine.cu
 * @brief CUDA kernels for combining expert outputs with routing weights
 *
 * After each expert has processed its assigned tokens, the combine step
 * performs a weighted gather: each token's output is the weighted sum of
 * its assigned experts' outputs, with weights from the router.
 *
 * This implements: output[i] = sum_k(weight[i][k] * expert_output[selected_k][i])
 */

#include "common/moe_layer.h"
#include "cuda_utils.h"
#include <vector>

namespace llm {

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Weighted gather of expert outputs back to token positions
 *
 * For each token, sums the outputs from its assigned experts weighted
 * by the router-computed weights.
 *
 * @param[out] output          Combined output [num_tokens, d_model]
 * @param[in]  expert_outputs  Per-expert outputs [num_experts, capacity, d_model]
 * @param[in]  expert_indices  Selected expert IDs [num_tokens, top_k]
 * @param[in]  expert_weights  Routing weights [num_tokens, top_k]
 * @param[in]  token_slots     Slot index for each (token, expert) pair [num_tokens, top_k]
 * @param[in]  num_tokens      Number of tokens
 * @param[in]  d_model         Model hidden dimension
 * @param[in]  top_k           Number of experts per token
 * @param[in]  capacity        Expert buffer capacity
 */
__global__ void expert_combine_kernel(
    float* output, const float* expert_outputs,
    const int* expert_indices, const float* expert_weights,
    const int* token_slots,
    int num_tokens, int d_model, int top_k, int num_experts, int capacity
) {
    int token_idx = blockIdx.x;
    int dim_idx = threadIdx.x;

    if (token_idx >= num_tokens || dim_idx >= d_model) return;

    float sum = 0.0f;
    for (int k = 0; k < top_k; k++) {
        int expert_id = expert_indices[token_idx * top_k + k];
        float weight = expert_weights[token_idx * top_k + k];
        int slot = token_slots[token_idx * top_k + k];

        if (expert_id >= 0 && expert_id < num_experts && slot >= 0 && slot < capacity) {
            size_t src_offset = static_cast<size_t>(expert_id) * capacity * d_model +
                               static_cast<size_t>(slot) * d_model + dim_idx;
            sum += weight * expert_outputs[src_offset];
        }
    }

    output[token_idx * d_model + dim_idx] = sum;
}

/**
 * @brief Simple weighted combine without slot tracking
 *
 * A simpler version that assumes expert outputs are stored directly
 * in token order (one output per token per expert slot), without
 * needing explicit slot tracking. This is used when the dispatch
 * maintains a token-to-slot mapping on the host.
 *
 * @param[out] output          Combined output [num_tokens, d_model]
 * @param[in]  expert_outputs  Expert outputs indexed by (token, k) [num_tokens * top_k, d_model]
 * @param[in]  expert_weights  Routing weights [num_tokens, top_k]
 * @param[in]  num_tokens      Number of tokens
 * @param[in]  d_model         Model dimension
 * @param[in]  top_k           Experts per token
 */
__global__ void expert_combine_simple_kernel(
    float* output, const float* expert_outputs,
    const float* expert_weights,
    int num_tokens, int d_model, int top_k
) {
    int token_idx = blockIdx.x;
    int dim_idx = threadIdx.x;

    if (token_idx >= num_tokens || dim_idx >= d_model) return;

    float sum = 0.0f;
    for (int k = 0; k < top_k; k++) {
        float weight = expert_weights[token_idx * top_k + k];
        size_t src_offset = static_cast<size_t>(token_idx * top_k + k) * d_model + dim_idx;
        sum += weight * expert_outputs[src_offset];
    }

    output[token_idx * d_model + dim_idx] = sum;
}

// ============================================================================
// MoE layer forward pass
// ============================================================================

void moe_layer_forward(float* output, const float* input,
                       const float* W_router,
                       const ExpertWeights& experts,
                       const MoELayerConfig& config,
                       int num_tokens,
                       float* aux_loss,
                       cudaStream_t stream) {
    int num_experts = config.router.num_experts;
    int d_model = config.d_model;
    int d_ff = config.d_ff;
    int top_k = config.router.top_k;

    // Step 1: Route tokens to experts
    RouterOutput routing = allocate_router_output(num_tokens, config.router);
    topk_route(routing, input, W_router, config.router, num_tokens, stream);

    // Step 2: For each selected expert, run the expert forward pass
    // We use the simple approach: process each (token, expert_slot) pair
    // and store results in a flat buffer [num_tokens * top_k, d_model]
    size_t total_pairs = static_cast<size_t>(num_tokens) * top_k;
    float* d_expert_outputs = nullptr;
    CHECK_CUDA(cudaMalloc(&d_expert_outputs, total_pairs * d_model * sizeof(float)));

    // Copy routing decisions to host for dispatch logic
    std::vector<int> h_indices(num_tokens * top_k);
    CHECK_CUDA(cudaMemcpy(h_indices.data(), routing.expert_indices,
                          num_tokens * top_k * sizeof(int), cudaMemcpyDeviceToHost));

    // Process each expert: gather its tokens, run forward, scatter back
    for (int e = 0; e < num_experts; e++) {
        // Find which (token, slot) pairs are assigned to this expert
        std::vector<int> assigned_tokens;
        std::vector<int> assigned_slots;
        for (int t = 0; t < num_tokens; t++) {
            for (int k = 0; k < top_k; k++) {
                if (h_indices[t * top_k + k] == e) {
                    assigned_tokens.push_back(t);
                    assigned_slots.push_back(t * top_k + k);
                }
            }
        }

        int n_assigned = static_cast<int>(assigned_tokens.size());
        if (n_assigned == 0) continue;

        // Gather input tokens for this expert
        float* d_expert_input = nullptr;
        float* d_expert_out = nullptr;
        CHECK_CUDA(cudaMalloc(&d_expert_input, n_assigned * d_model * sizeof(float)));
        CHECK_CUDA(cudaMalloc(&d_expert_out, n_assigned * d_model * sizeof(float)));

        for (int i = 0; i < n_assigned; i++) {
            int t = assigned_tokens[i];
            CHECK_CUDA(cudaMemcpyAsync(
                d_expert_input + i * d_model,
                input + t * d_model,
                d_model * sizeof(float),
                cudaMemcpyDeviceToDevice, stream));
        }

        // Run expert forward
        expert_forward(d_expert_out, d_expert_input,
                      experts.W_gate[e], experts.W_up[e], experts.W_down[e],
                      d_model, d_ff, n_assigned, stream);

        // Scatter results to output buffer
        for (int i = 0; i < n_assigned; i++) {
            int slot = assigned_slots[i];
            CHECK_CUDA(cudaMemcpyAsync(
                d_expert_outputs + slot * d_model,
                d_expert_out + i * d_model,
                d_model * sizeof(float),
                cudaMemcpyDeviceToDevice, stream));
        }

        cudaFree(d_expert_input);
        cudaFree(d_expert_out);
    }

    // Step 3: Combine expert outputs weighted by routing weights
    int block_dim = (d_model <= 1024) ? d_model : 1024;
    expert_combine_simple_kernel<<<num_tokens, block_dim, 0, stream>>>(
        output, d_expert_outputs, routing.expert_weights,
        num_tokens, d_model, top_k);

    // Step 4: Compute auxiliary load balancing loss (optional)
    if (aux_loss != nullptr) {
        // Compute on host for simplicity: importance-weighted loss
        std::vector<float> h_gate(num_tokens * num_experts);
        CHECK_CUDA(cudaMemcpy(h_gate.data(), routing.gate_logits,
                              num_tokens * num_experts * sizeof(float),
                              cudaMemcpyDeviceToHost));

        float loss = 0.0f;
        for (int e = 0; e < num_experts; e++) {
            float fraction = 0.0f;
            float importance = 0.0f;
            for (int t = 0; t < num_tokens; t++) {
                importance += h_gate[t * num_experts + e];
                for (int k = 0; k < top_k; k++) {
                    if (h_indices[t * top_k + k] == e) {
                        fraction += 1.0f;
                        break;
                    }
                }
            }
            fraction /= num_tokens;
            importance /= num_tokens;
            loss += fraction * importance;
        }
        loss *= num_experts * config.aux_loss_weight;

        CHECK_CUDA(cudaMemcpy(aux_loss, &loss, sizeof(float), cudaMemcpyHostToDevice));
    }

    CHECK_CUDA(cudaStreamSynchronize(stream));

    cudaFree(d_expert_outputs);
    free_router_output(routing);
}

} // namespace llm
