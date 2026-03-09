/**
 * @file similarity_kernels.cu
 * @brief GPU cosine similarity kernels for expert prediction
 *
 * Implements efficient cosine similarity computation between a hidden
 * state vector and a set of expert centroid vectors. Used by the
 * prefetching system to predict which experts will be needed.
 */

#include "common/attention_similarity.h"
#include <cuda_runtime.h>
#include <cmath>

namespace llm {

/**
 * @brief Kernel: compute dot product and norms for cosine similarity
 *
 * Each block handles one expert. Uses shared memory reduction to
 * compute dot(hidden, centroid[expert]) and ||centroid[expert]||.
 *
 * @param[out] similarities     Output similarity scores [num_experts]
 * @param[in]  hidden_state     Hidden state vector [d_model]
 * @param[in]  expert_centroids Expert centroids [num_experts x d_model]
 * @param[in]  d_model          Dimension of the hidden state
 * @param[in]  hidden_norm      Pre-computed ||hidden_state||
 */
__global__ void cosine_similarity_kernel(float* similarities,
                                         const float* hidden_state,
                                         const float* expert_centroids,
                                         int d_model,
                                         float hidden_norm) {
    extern __shared__ float sdata[];

    int expert_id = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    const float* centroid = expert_centroids + expert_id * d_model;

    // Each thread accumulates partial dot product and centroid norm
    float dot_sum = 0.0f;
    float norm_sum = 0.0f;

    for (int i = tid; i < d_model; i += block_size) {
        float h = hidden_state[i];
        float c = centroid[i];
        dot_sum += h * c;
        norm_sum += c * c;
    }

    // Store in shared memory: first half for dot products, second half for norms
    sdata[tid] = dot_sum;
    sdata[tid + block_size] = norm_sum;
    __syncthreads();

    // Reduction
    for (int s = block_size / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
            sdata[tid + block_size] += sdata[tid + block_size + s];
        }
        __syncthreads();
    }

    if (tid == 0) {
        float dot = sdata[0];
        float centroid_norm = sqrtf(sdata[block_size]);
        float denom = hidden_norm * centroid_norm;
        similarities[expert_id] = (denom > 1e-8f) ? (dot / denom) : 0.0f;
    }
}

/**
 * @brief Kernel: compute L2 norm of a vector
 *
 * @param[out] result  Scalar output for the norm
 * @param[in]  vec     Input vector
 * @param[in]  n       Length of the vector
 */
__global__ void vector_norm_kernel(float* result, const float* vec, int n) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int block_size = blockDim.x;

    float sum = 0.0f;
    for (int i = tid; i < n; i += block_size) {
        float v = vec[i];
        sum += v * v;
    }

    sdata[tid] = sum;
    __syncthreads();

    for (int s = block_size / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    if (tid == 0) {
        result[0] = sqrtf(sdata[0]);
    }
}

/**
 * @brief Kernel: select top-k expert indices by highest similarity
 *
 * Simple O(num_experts * top_k) selection suitable for small expert counts.
 * Single-threaded kernel (launched with 1 thread).
 *
 * @param[out] predicted   Output top-k expert indices
 * @param[in]  similarities Similarity scores [num_experts]
 * @param[in]  num_experts  Total number of experts
 * @param[in]  top_k        Number of experts to select
 */
__global__ void top_k_experts_kernel(int* predicted, const float* similarities,
                                     int num_experts, int top_k) {
    // Simple selection (single thread)
    for (int k = 0; k < top_k; ++k) {
        float best_val = -1e30f;
        int best_idx = 0;
        for (int i = 0; i < num_experts; ++i) {
            // Skip already selected
            bool already_selected = false;
            for (int j = 0; j < k; ++j) {
                if (predicted[j] == i) {
                    already_selected = true;
                    break;
                }
            }
            if (!already_selected && similarities[i] > best_val) {
                best_val = similarities[i];
                best_idx = i;
            }
        }
        predicted[k] = best_idx;
    }
}

void compute_expert_similarity(float* similarities, const float* hidden_state,
                              const float* expert_centroids,
                              int d_model, int num_experts,
                              cudaStream_t stream) {
    // Compute hidden state norm
    float* d_hidden_norm;
    cudaMalloc(&d_hidden_norm, sizeof(float));

    int norm_threads = 256;
    vector_norm_kernel<<<1, norm_threads, norm_threads * sizeof(float), stream>>>(
        d_hidden_norm, hidden_state, d_model);

    // Copy norm to host for the similarity kernel
    float hidden_norm;
    cudaMemcpyAsync(&hidden_norm, d_hidden_norm, sizeof(float),
                    cudaMemcpyDeviceToHost, stream);
    cudaStreamSynchronize(stream);

    // Compute cosine similarity for each expert
    int sim_threads = 256;
    size_t shared_size = 2 * sim_threads * sizeof(float);
    cosine_similarity_kernel<<<num_experts, sim_threads, shared_size, stream>>>(
        similarities, hidden_state, expert_centroids, d_model, hidden_norm);

    cudaFree(d_hidden_norm);
}

void predict_experts(int* predicted_experts, const float* similarities,
                    int num_experts, int top_k,
                    cudaStream_t stream) {
    top_k_experts_kernel<<<1, 1, 0, stream>>>(
        predicted_experts, similarities, num_experts, top_k);
}

} // namespace llm
