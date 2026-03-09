/**
 * @file expert_dispatch.cu
 * @brief CUDA kernels for dispatching tokens to their assigned experts
 *
 * After the router selects top-k experts per token, the dispatch step
 * scatters each token's hidden state to the appropriate expert's input
 * buffer. Each token may be sent to multiple experts (top-k), so the
 * dispatch creates top_k copies of each token's data.
 */

#include "common/topk_router.h"
#include "common/expert_network.h"
#include "cuda_utils.h"
#include <cmath>
#include <vector>
#include <random>

namespace llm {

// ============================================================================
// GPU Kernels
// ============================================================================

/**
 * @brief Scatter tokens to expert input buffers
 *
 * For each (token, expert_slot) pair, copies the token's hidden state
 * into the corresponding expert's input buffer at the assigned position.
 *
 * @param[out] expert_inputs   Expert input buffers [num_experts, capacity, d_model]
 * @param[out] expert_counts   Number of tokens assigned to each expert [num_experts]
 * @param[in]  input           Input token hidden states [num_tokens, d_model]
 * @param[in]  expert_indices  Router-selected expert IDs [num_tokens, top_k]
 * @param[in]  num_tokens      Total number of tokens
 * @param[in]  d_model         Model hidden dimension
 * @param[in]  top_k           Number of experts per token
 * @param[in]  num_experts     Total number of experts
 * @param[in]  capacity        Max tokens per expert
 */
__global__ void expert_dispatch_kernel(
    float* expert_inputs, int* expert_counts,
    const float* input, const int* expert_indices,
    int num_tokens, int d_model, int top_k, int num_experts, int capacity
) {
    int token_idx = blockIdx.x;
    int dim_idx = threadIdx.x;

    if (token_idx >= num_tokens || dim_idx >= d_model) return;

    for (int k = 0; k < top_k; k++) {
        int expert_id = expert_indices[token_idx * top_k + k];
        if (expert_id < 0 || expert_id >= num_experts) continue;

        // Atomically get the slot index for this expert
        // (Only thread 0 in each block does the atomic for this token+k)
        __shared__ int slot;
        if (dim_idx == 0) {
            slot = atomicAdd(&expert_counts[expert_id], 1);
        }
        __syncthreads();

        if (slot < capacity) {
            size_t dst_offset = static_cast<size_t>(expert_id) * capacity * d_model +
                               static_cast<size_t>(slot) * d_model + dim_idx;
            expert_inputs[dst_offset] = input[token_idx * d_model + dim_idx];
        }
    }
}

/**
 * @brief Count tokens per expert (pre-pass for dispatch planning)
 *
 * Counts how many tokens are assigned to each expert so that buffer
 * sizes can be determined before the actual dispatch.
 *
 * @param[out] counts          Per-expert token counts [num_experts]
 * @param[in]  expert_indices  Router-selected expert IDs [num_tokens, top_k]
 * @param[in]  num_tokens      Number of tokens
 * @param[in]  top_k           Experts per token
 * @param[in]  num_experts     Total experts
 */
__global__ void count_tokens_per_expert_kernel(
    int* counts, const int* expert_indices,
    int num_tokens, int top_k, int num_experts
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total_assignments = num_tokens * top_k;
    if (idx >= total_assignments) return;

    int expert_id = expert_indices[idx];
    if (expert_id >= 0 && expert_id < num_experts) {
        atomicAdd(&counts[expert_id], 1);
    }
}

// ============================================================================
// Expert network implementation
// ============================================================================

/**
 * @brief Naive matmul for expert forward: Y = X * W^T
 */
__global__ void expert_matmul_kernel(
    float* Y, const float* X, const float* W,
    int M, int K, int N
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; k++) {
            sum += X[row * K + k] * W[col * K + k];
        }
        Y[row * N + col] = sum;
    }
}

/**
 * @brief Fused SiLU gate and multiply for expert SwiGLU FFN
 */
__global__ void expert_swiglu_kernel(
    float* output, const float* gate, const float* up, int total
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < total) {
        float g = gate[idx];
        float silu_g = g / (1.0f + expf(-g));
        output[idx] = silu_g * up[idx];
    }
}

void expert_forward(float* output, const float* input,
                    const float* W_gate, const float* W_up, const float* W_down,
                    int d_model, int d_ff, int num_tokens,
                    cudaStream_t stream) {
    if (num_tokens <= 0) return;

    // Allocate intermediate buffers
    float *d_gate = nullptr, *d_up = nullptr, *d_fused = nullptr;
    CHECK_CUDA(cudaMalloc(&d_gate, num_tokens * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_up, num_tokens * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_fused, num_tokens * d_ff * sizeof(float)));

    dim3 mm_block(16, 16);

    // gate = input * W_gate^T  [num_tokens, d_ff]
    dim3 gate_grid((num_tokens + 15) / 16, (d_ff + 15) / 16);
    expert_matmul_kernel<<<gate_grid, mm_block, 0, stream>>>(
        d_gate, input, W_gate, num_tokens, d_model, d_ff);

    // up = input * W_up^T  [num_tokens, d_ff]
    expert_matmul_kernel<<<gate_grid, mm_block, 0, stream>>>(
        d_up, input, W_up, num_tokens, d_model, d_ff);

    // fused = SiLU(gate) * up
    int total_elements = num_tokens * d_ff;
    int act_threads = 256;
    int act_blocks = (total_elements + act_threads - 1) / act_threads;
    expert_swiglu_kernel<<<act_blocks, act_threads, 0, stream>>>(
        d_fused, d_gate, d_up, total_elements);

    // output = fused * W_down^T  [num_tokens, d_model]
    dim3 down_grid((num_tokens + 15) / 16, (d_model + 15) / 16);
    expert_matmul_kernel<<<down_grid, mm_block, 0, stream>>>(
        output, d_fused, W_down, num_tokens, d_ff, d_model);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    cudaFree(d_gate);
    cudaFree(d_up);
    cudaFree(d_fused);
}

// ============================================================================
// Expert weight management
// ============================================================================

ExpertWeights allocate_expert_weights(int num_experts, int d_model, int d_ff) {
    ExpertWeights w = {};
    w.num_experts = num_experts;
    w.d_model = d_model;
    w.d_ff = d_ff;

    // Allocate host arrays for device pointers
    w.W_gate = new float*[num_experts];
    w.W_up = new float*[num_experts];
    w.W_down = new float*[num_experts];

    size_t gate_up_size = static_cast<size_t>(d_ff) * d_model * sizeof(float);
    size_t down_size = static_cast<size_t>(d_model) * d_ff * sizeof(float);

    for (int e = 0; e < num_experts; e++) {
        CHECK_CUDA(cudaMalloc(&w.W_gate[e], gate_up_size));
        CHECK_CUDA(cudaMalloc(&w.W_up[e], gate_up_size));
        CHECK_CUDA(cudaMalloc(&w.W_down[e], down_size));
    }

    return w;
}

void free_expert_weights(ExpertWeights& w) {
    if (w.W_gate) {
        for (int e = 0; e < w.num_experts; e++) {
            if (w.W_gate[e]) cudaFree(w.W_gate[e]);
            if (w.W_up[e]) cudaFree(w.W_up[e]);
            if (w.W_down[e]) cudaFree(w.W_down[e]);
        }
        delete[] w.W_gate; w.W_gate = nullptr;
        delete[] w.W_up; w.W_up = nullptr;
        delete[] w.W_down; w.W_down = nullptr;
    }
}

void initialize_expert_weights(ExpertWeights& w, unsigned int seed) {
    std::default_random_engine gen(seed);
    float stddev_gate = 1.0f / std::sqrt(static_cast<float>(w.d_model));
    float stddev_down = 1.0f / std::sqrt(static_cast<float>(w.d_ff));

    for (int e = 0; e < w.num_experts; e++) {
        size_t gate_up_count = static_cast<size_t>(w.d_ff) * w.d_model;
        size_t down_count = static_cast<size_t>(w.d_model) * w.d_ff;

        // Gate weights
        {
            std::normal_distribution<float> dist(0.0f, stddev_gate);
            std::vector<float> h_data(gate_up_count);
            for (auto& v : h_data) v = dist(gen);
            CHECK_CUDA(cudaMemcpy(w.W_gate[e], h_data.data(),
                                  gate_up_count * sizeof(float), cudaMemcpyHostToDevice));
        }
        // Up weights
        {
            std::normal_distribution<float> dist(0.0f, stddev_gate);
            std::vector<float> h_data(gate_up_count);
            for (auto& v : h_data) v = dist(gen);
            CHECK_CUDA(cudaMemcpy(w.W_up[e], h_data.data(),
                                  gate_up_count * sizeof(float), cudaMemcpyHostToDevice));
        }
        // Down weights
        {
            std::normal_distribution<float> dist(0.0f, stddev_down);
            std::vector<float> h_data(down_count);
            for (auto& v : h_data) v = dist(gen);
            CHECK_CUDA(cudaMemcpy(w.W_down[e], h_data.data(),
                                  down_count * sizeof(float), cudaMemcpyHostToDevice));
        }
    }
}

} // namespace llm
