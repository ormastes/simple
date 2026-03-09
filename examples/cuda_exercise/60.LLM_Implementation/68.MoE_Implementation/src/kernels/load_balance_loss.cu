/**
 * @file load_balance_loss.cu
 * @brief CUDA kernels for MoE load balancing auxiliary loss
 *
 * Implements the auxiliary loss function that encourages balanced expert
 * utilization. Without this loss, the router may collapse to always
 * selecting the same few experts, leaving others unused.
 *
 * The loss is computed as:
 *   L_aux = alpha * num_experts * sum_e(f_e * P_e)
 *
 * where f_e is the fraction of tokens routed to expert e, and P_e is
 * the mean routing probability for expert e across all tokens.
 */

#include "common/topk_router.h"
#include "cuda_utils.h"

namespace llm {

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Compute per-expert routing fraction and mean probability
 *
 * For each expert, computes:
 * - fraction[e]: fraction of tokens that selected expert e (via top-k)
 * - mean_prob[e]: average softmax probability assigned to expert e
 *
 * @param[out] fraction       Per-expert selection fraction [num_experts]
 * @param[out] mean_prob      Per-expert mean probability [num_experts]
 * @param[in]  expert_indices Selected expert IDs [num_tokens, top_k]
 * @param[in]  gate_probs     Softmax routing probabilities [num_tokens, num_experts]
 * @param[in]  num_tokens     Number of tokens
 * @param[in]  num_experts    Number of experts
 * @param[in]  top_k          Experts per token
 */
__global__ void compute_expert_stats_kernel(
    float* fraction, float* mean_prob,
    const int* expert_indices, const float* gate_probs,
    int num_tokens, int num_experts, int top_k
) {
    int expert_id = blockIdx.x * blockDim.x + threadIdx.x;
    if (expert_id >= num_experts) return;

    float count = 0.0f;
    float prob_sum = 0.0f;

    for (int t = 0; t < num_tokens; t++) {
        // Check if this expert was selected for token t
        for (int k = 0; k < top_k; k++) {
            if (expert_indices[t * top_k + k] == expert_id) {
                count += 1.0f;
                break;
            }
        }

        // Sum the gate probability for this expert
        prob_sum += gate_probs[t * num_experts + expert_id];
    }

    float inv_n = 1.0f / static_cast<float>(num_tokens);
    fraction[expert_id] = count * inv_n;
    mean_prob[expert_id] = prob_sum * inv_n;
}

/**
 * @brief Compute the load balancing loss from per-expert statistics
 *
 * L_aux = alpha * num_experts * sum_e(fraction[e] * mean_prob[e])
 *
 * @param[out] loss          Scalar loss value [1]
 * @param[in]  fraction      Per-expert selection fraction [num_experts]
 * @param[in]  mean_prob     Per-expert mean probability [num_experts]
 * @param[in]  num_experts   Number of experts
 * @param[in]  alpha         Loss weight coefficient
 */
__global__ void load_balance_loss_kernel(
    float* loss, const float* fraction, const float* mean_prob,
    int num_experts, float alpha
) {
    // Single-thread kernel for reduction
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    float sum = 0.0f;
    for (int e = 0; e < num_experts; e++) {
        sum += fraction[e] * mean_prob[e];
    }

    loss[0] = alpha * static_cast<float>(num_experts) * sum;
}

/**
 * @brief Compute per-expert importance scores
 *
 * The importance of each expert is the sum of its routing probabilities
 * across all tokens. This is used for monitoring expert utilization.
 *
 * @param[out] importance     Per-expert importance [num_experts]
 * @param[in]  gate_probs     Softmax probabilities [num_tokens, num_experts]
 * @param[in]  num_tokens     Number of tokens
 * @param[in]  num_experts    Number of experts
 */
__global__ void compute_expert_importance_kernel(
    float* importance, const float* gate_probs,
    int num_tokens, int num_experts
) {
    int expert_id = blockIdx.x * blockDim.x + threadIdx.x;
    if (expert_id >= num_experts) return;

    float sum = 0.0f;
    for (int t = 0; t < num_tokens; t++) {
        sum += gate_probs[t * num_experts + expert_id];
    }
    importance[expert_id] = sum;
}

// ============================================================================
// Launch wrapper
// ============================================================================

/**
 * @brief Compute load balancing auxiliary loss
 *
 * Computes the loss that encourages balanced expert usage.
 * This function is called from moe_layer_forward() in expert_combine.cu.
 *
 * @param[out] d_loss         Scalar loss on device [1]
 * @param[in]  routing        Router output with expert_indices and gate_logits
 * @param[in]  config         Router configuration
 * @param[in]  alpha          Loss weight
 * @param[in]  stream         CUDA stream
 */
void compute_load_balance_loss(float* d_loss, const RouterOutput& routing,
                               const RouterConfig& config, float alpha,
                               cudaStream_t stream) {
    int num_tokens = routing.num_tokens;
    int num_experts = config.num_experts;
    int top_k = config.top_k;

    // Allocate temporary buffers
    float* d_fraction = nullptr;
    float* d_mean_prob = nullptr;
    CHECK_CUDA(cudaMalloc(&d_fraction, num_experts * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_mean_prob, num_experts * sizeof(float)));

    // Compute per-expert statistics
    int threads = 256;
    int blocks = (num_experts + threads - 1) / threads;
    compute_expert_stats_kernel<<<blocks, threads, 0, stream>>>(
        d_fraction, d_mean_prob,
        routing.expert_indices, routing.gate_logits,
        num_tokens, num_experts, top_k);

    // Compute loss
    load_balance_loss_kernel<<<1, 1, 0, stream>>>(
        d_loss, d_fraction, d_mean_prob, num_experts, alpha);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    cudaFree(d_fraction);
    cudaFree(d_mean_prob);
}

} // namespace llm
