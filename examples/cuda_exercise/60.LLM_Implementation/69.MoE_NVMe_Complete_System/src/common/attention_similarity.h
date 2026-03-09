/**
 * @file attention_similarity.h
 * @brief Attention-based similarity for expert prediction
 *
 * Provides cosine similarity computation between hidden states and
 * expert centroid vectors, enabling predictive prefetching of expert
 * weights from NVMe storage before they are needed.
 */
#pragma once
#include <cuda_runtime.h>

namespace llm {

/**
 * @brief Compute cosine similarity between a hidden state and expert centroids
 *
 * For each expert, computes:
 *   similarity[i] = dot(hidden_state, centroid[i]) / (||hidden_state|| * ||centroid[i]||)
 *
 * @param[out] similarities  Output array of size num_experts (device memory)
 * @param[in]  hidden_state  Current hidden state vector of size d_model (device memory)
 * @param[in]  expert_centroids  Expert centroid matrix [num_experts x d_model] (device memory)
 * @param[in]  d_model       Dimension of the model hidden state
 * @param[in]  num_experts   Number of experts
 * @param[in]  stream        CUDA stream for async execution
 */
void compute_expert_similarity(float* similarities, const float* hidden_state,
                              const float* expert_centroids,
                              int d_model, int num_experts,
                              cudaStream_t stream = 0);

/**
 * @brief Predict which experts will be needed for prefetching
 *
 * Selects the top-k experts with highest similarity scores for
 * prefetching from NVMe storage.
 *
 * @param[out] predicted_experts  Output array of top_k expert indices (device memory)
 * @param[in]  similarities       Similarity scores for all experts (device memory)
 * @param[in]  num_experts        Total number of experts
 * @param[in]  top_k              Number of experts to predict
 * @param[in]  stream             CUDA stream for async execution
 */
void predict_experts(int* predicted_experts, const float* similarities,
                    int num_experts, int top_k,
                    cudaStream_t stream = 0);

} // namespace llm
