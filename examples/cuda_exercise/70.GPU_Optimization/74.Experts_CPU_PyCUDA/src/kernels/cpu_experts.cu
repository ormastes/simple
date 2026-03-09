/**
 * @file cpu_experts.cu
 * @brief CPU-based Mixture of Experts (MoE) implementations for baseline comparison
 *
 * This file implements various CPU MoE algorithms:
 * - Top-k gating with softmax normalization
 * - Single expert FFN with GELU activation
 * - Complete MoE forward pass (naive and parallel)
 * - GELU activation function
 *
 * All functions use flat buffer layout for expert weights to enable
 * straightforward ctypes bindings from Python.
 */

#include "cpu_experts.h"
#include <algorithm>
#include <cmath>
#include <vector>
#include <numeric>

#ifdef HAS_OPENMP
#include <omp.h>
#endif

/**
 * @brief GELU activation function
 *
 * Computes GELU(x) = x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 * This is the standard approximation used in GPT-2 and BERT.
 *
 * @param[out] output  Output tensor [n]
 * @param[in]  input   Input tensor [n]
 * @param[in]  n       Number of elements
 */
extern "C" void cpu_gelu(float* output, const float* input, int n) {
    const float sqrt_2_over_pi = 0.7978845608f;  // sqrt(2/pi)
    const float coeff = 0.044715f;

    for (int i = 0; i < n; i++) {
        float x = input[i];
        float x3 = x * x * x;
        float inner = sqrt_2_over_pi * (x + coeff * x3);
        output[i] = 0.5f * x * (1.0f + tanhf(inner));
    }
}

/**
 * @brief Top-k gating with softmax normalization
 *
 * For each token in the batch:
 * 1. Compute softmax over all expert logits
 * 2. Select top_k experts with highest softmax probabilities
 * 3. Re-normalize selected weights to sum to 1
 *
 * @param[out] expert_indices  Selected expert indices [batch_size * top_k]
 * @param[out] expert_weights  Normalized weights [batch_size * top_k]
 * @param[in]  gate_logits     Raw logits [batch_size * num_experts]
 * @param[in]  batch_size      Number of tokens
 * @param[in]  num_experts     Total number of experts
 * @param[in]  top_k           Number of experts to select
 */
extern "C" void cpu_topk_gating(int* expert_indices, float* expert_weights,
                                const float* gate_logits, int batch_size,
                                int num_experts, int top_k) {
    for (int b = 0; b < batch_size; b++) {
        const float* logits = &gate_logits[b * num_experts];

        // Find max for numerical stability in softmax
        float max_logit = logits[0];
        for (int e = 1; e < num_experts; e++) {
            if (logits[e] > max_logit) {
                max_logit = logits[e];
            }
        }

        // Compute softmax probabilities
        std::vector<float> probs(num_experts);
        float sum_exp = 0.0f;
        for (int e = 0; e < num_experts; e++) {
            probs[e] = expf(logits[e] - max_logit);
            sum_exp += probs[e];
        }
        for (int e = 0; e < num_experts; e++) {
            probs[e] /= sum_exp;
        }

        // Create index array and partial sort to find top_k
        std::vector<int> indices(num_experts);
        std::iota(indices.begin(), indices.end(), 0);

        std::partial_sort(indices.begin(), indices.begin() + top_k, indices.end(),
            [&probs](int a, int b_idx) { return probs[a] > probs[b_idx]; });

        // Extract top_k indices and re-normalize weights
        float topk_sum = 0.0f;
        for (int k = 0; k < top_k; k++) {
            int idx = indices[k];
            expert_indices[b * top_k + k] = idx;
            expert_weights[b * top_k + k] = probs[idx];
            topk_sum += probs[idx];
        }

        // Re-normalize weights over selected experts
        if (topk_sum > 0.0f) {
            for (int k = 0; k < top_k; k++) {
                expert_weights[b * top_k + k] /= topk_sum;
            }
        }
    }
}

/**
 * @brief Single expert FFN: output = GELU(input * W1^T + b1) * W2^T + b2
 *
 * Two-layer feed-forward network with GELU activation.
 * Flat buffer layout:
 *   W1: [num_experts, d_ff, d_model] -> expert_idx selects [d_ff, d_model] slice
 *   b1: [num_experts, d_ff]
 *   W2: [num_experts, d_model, d_ff] -> expert_idx selects [d_model, d_ff] slice
 *   b2: [num_experts, d_model]
 *
 * @param[out] output       Output [batch_size * d_model]
 * @param[in]  input        Input [batch_size * d_model]
 * @param[in]  weights_1    All W1 [num_experts * d_ff * d_model]
 * @param[in]  bias_1       All b1 [num_experts * d_ff]
 * @param[in]  weights_2    All W2 [num_experts * d_model * d_ff]
 * @param[in]  bias_2       All b2 [num_experts * d_model]
 * @param[in]  batch_size   Number of tokens
 * @param[in]  d_model      Model dimension
 * @param[in]  d_ff         Hidden dimension
 * @param[in]  expert_idx   Which expert to use
 * @param[in]  num_experts  Total experts (for offset calculation)
 */
extern "C" void cpu_expert_ffn(float* output, const float* input,
                               const float* weights_1, const float* bias_1,
                               const float* weights_2, const float* bias_2,
                               int batch_size, int d_model, int d_ff,
                               int expert_idx, int num_experts) {
    // Compute offsets into flat buffers for this expert
    const float* W1 = &weights_1[expert_idx * d_ff * d_model];
    const float* b1 = &bias_1[expert_idx * d_ff];
    const float* W2 = &weights_2[expert_idx * d_model * d_ff];
    const float* b2 = &bias_2[expert_idx * d_model];

    // Allocate hidden layer buffer
    std::vector<float> hidden(batch_size * d_ff);

    // First linear layer: hidden = input * W1^T + b1, then GELU
    for (int b = 0; b < batch_size; b++) {
        for (int f = 0; f < d_ff; f++) {
            float sum = b1[f];
            for (int d = 0; d < d_model; d++) {
                sum += input[b * d_model + d] * W1[f * d_model + d];
            }
            // Apply GELU inline
            float x = sum;
            float x3 = x * x * x;
            hidden[b * d_ff + f] = 0.5f * x * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x3)));
        }
    }

    // Second linear layer: output = hidden * W2^T + b2
    for (int b = 0; b < batch_size; b++) {
        for (int d = 0; d < d_model; d++) {
            float sum = b2[d];
            for (int f = 0; f < d_ff; f++) {
                sum += hidden[b * d_ff + f] * W2[d * d_ff + f];
            }
            output[b * d_model + d] = sum;
        }
    }
}

/**
 * @brief Complete MoE forward pass (naive, single-threaded)
 *
 * For each token:
 * 1. Compute gate logits: gate_logits[b, e] = dot(input[b], gate_weights[e])
 * 2. Select top_k experts via cpu_topk_gating
 * 3. Compute expert FFN for each selected expert
 * 4. Weighted sum of expert outputs
 *
 * @param[out] output            Output [batch_size * d_model]
 * @param[in]  input             Input [batch_size * d_model]
 * @param[in]  gate_weights      Gate weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All W1 [num_experts * d_ff * d_model]
 * @param[in]  expert_bias_1     All b1 [num_experts * d_ff]
 * @param[in]  expert_weights_2  All W2 [num_experts * d_model * d_ff]
 * @param[in]  expert_bias_2     All b2 [num_experts * d_model]
 * @param[in]  batch_size        Batch size
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Hidden dimension
 * @param[in]  num_experts       Number of experts
 * @param[in]  top_k             Experts per token
 */
extern "C" void cpu_moe_forward(float* output, const float* input,
                                const float* gate_weights,
                                const float* expert_weights_1, const float* expert_bias_1,
                                const float* expert_weights_2, const float* expert_bias_2,
                                int batch_size, int d_model, int d_ff,
                                int num_experts, int top_k) {
    // Step 1: Compute gate logits for all tokens
    std::vector<float> gate_logits(batch_size * num_experts);
    for (int b = 0; b < batch_size; b++) {
        for (int e = 0; e < num_experts; e++) {
            float sum = 0.0f;
            for (int d = 0; d < d_model; d++) {
                sum += input[b * d_model + d] * gate_weights[e * d_model + d];
            }
            gate_logits[b * num_experts + e] = sum;
        }
    }

    // Step 2: Select top_k experts per token
    std::vector<int> expert_indices(batch_size * top_k);
    std::vector<float> expert_wts(batch_size * top_k);
    cpu_topk_gating(expert_indices.data(), expert_wts.data(),
                    gate_logits.data(), batch_size, num_experts, top_k);

    // Step 3: For each token, compute weighted expert outputs
    std::vector<float> expert_output(d_model);

    for (int b = 0; b < batch_size; b++) {
        // Zero initialize output for this token
        for (int d = 0; d < d_model; d++) {
            output[b * d_model + d] = 0.0f;
        }

        // Process through top_k experts
        for (int k = 0; k < top_k; k++) {
            int eidx = expert_indices[b * top_k + k];
            float weight = expert_wts[b * top_k + k];

            // Compute expert FFN for this single token
            cpu_expert_ffn(expert_output.data(), &input[b * d_model],
                          expert_weights_1, expert_bias_1,
                          expert_weights_2, expert_bias_2,
                          1, d_model, d_ff, eidx, num_experts);

            // Accumulate weighted output
            for (int d = 0; d < d_model; d++) {
                output[b * d_model + d] += weight * expert_output[d];
            }
        }
    }
}

/**
 * @brief Parallel MoE forward pass using OpenMP
 *
 * Parallelizes the batch dimension using OpenMP. Each thread processes
 * different tokens independently. Falls back to naive if OpenMP is not available.
 *
 * @param[out] output            Output [batch_size * d_model]
 * @param[in]  input             Input [batch_size * d_model]
 * @param[in]  gate_weights      Gate weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All W1 [num_experts * d_ff * d_model]
 * @param[in]  expert_bias_1     All b1 [num_experts * d_ff]
 * @param[in]  expert_weights_2  All W2 [num_experts * d_model * d_ff]
 * @param[in]  expert_bias_2     All b2 [num_experts * d_model]
 * @param[in]  batch_size        Batch size
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Hidden dimension
 * @param[in]  num_experts       Number of experts
 * @param[in]  top_k             Experts per token
 * @param[in]  num_threads       Number of threads (-1 for all available)
 */
extern "C" void cpu_moe_forward_parallel(float* output, const float* input,
                                         const float* gate_weights,
                                         const float* expert_weights_1, const float* expert_bias_1,
                                         const float* expert_weights_2, const float* expert_bias_2,
                                         int batch_size, int d_model, int d_ff,
                                         int num_experts, int top_k,
                                         int num_threads) {
#ifdef HAS_OPENMP
    if (num_threads > 0) {
        omp_set_num_threads(num_threads);
    }

    // Step 1: Compute gate logits (parallelized over batch)
    std::vector<float> gate_logits(batch_size * num_experts);

    #pragma omp parallel for
    for (int b = 0; b < batch_size; b++) {
        for (int e = 0; e < num_experts; e++) {
            float sum = 0.0f;
            for (int d = 0; d < d_model; d++) {
                sum += input[b * d_model + d] * gate_weights[e * d_model + d];
            }
            gate_logits[b * num_experts + e] = sum;
        }
    }

    // Step 2: Select top_k experts per token
    std::vector<int> expert_indices(batch_size * top_k);
    std::vector<float> expert_wts(batch_size * top_k);
    cpu_topk_gating(expert_indices.data(), expert_wts.data(),
                    gate_logits.data(), batch_size, num_experts, top_k);

    // Step 3: Process tokens in parallel
    #pragma omp parallel for
    for (int b = 0; b < batch_size; b++) {
        std::vector<float> expert_output(d_model);

        // Zero initialize output for this token
        for (int d = 0; d < d_model; d++) {
            output[b * d_model + d] = 0.0f;
        }

        // Process through top_k experts
        for (int k = 0; k < top_k; k++) {
            int eidx = expert_indices[b * top_k + k];
            float weight = expert_wts[b * top_k + k];

            cpu_expert_ffn(expert_output.data(), &input[b * d_model],
                          expert_weights_1, expert_bias_1,
                          expert_weights_2, expert_bias_2,
                          1, d_model, d_ff, eidx, num_experts);

            for (int d = 0; d < d_model; d++) {
                output[b * d_model + d] += weight * expert_output[d];
            }
        }
    }
#else
    // Fallback to naive if OpenMP not available
    cpu_moe_forward(output, input, gate_weights,
                    expert_weights_1, expert_bias_1,
                    expert_weights_2, expert_bias_2,
                    batch_size, d_model, d_ff, num_experts, top_k);
#endif
}

/**
 * @brief Timed MoE forward pass
 *
 * Runs the MoE forward pass using the specified method and returns
 * the elapsed wall-clock time in milliseconds.
 *
 * @param[out] output            Output [batch_size * d_model]
 * @param[in]  input             Input [batch_size * d_model]
 * @param[in]  gate_weights      Gate weights [num_experts * d_model]
 * @param[in]  expert_weights_1  All W1
 * @param[in]  expert_bias_1     All b1
 * @param[in]  expert_weights_2  All W2
 * @param[in]  expert_bias_2     All b2
 * @param[in]  batch_size        Batch size
 * @param[in]  d_model           Model dimension
 * @param[in]  d_ff              Hidden dimension
 * @param[in]  num_experts       Number of experts
 * @param[in]  top_k             Experts per token
 * @param[in]  method            "naive" or "parallel"
 * @return     Elapsed time in milliseconds
 */
extern "C" float cpu_moe_timed(float* output, const float* input,
                               const float* gate_weights,
                               const float* expert_weights_1, const float* expert_bias_1,
                               const float* expert_weights_2, const float* expert_bias_2,
                               int batch_size, int d_model, int d_ff,
                               int num_experts, int top_k,
                               const char* method) {
    auto start = std::chrono::high_resolution_clock::now();

    if (strcmp(method, "naive") == 0) {
        cpu_moe_forward(output, input, gate_weights,
                       expert_weights_1, expert_bias_1,
                       expert_weights_2, expert_bias_2,
                       batch_size, d_model, d_ff, num_experts, top_k);
    } else if (strcmp(method, "parallel") == 0) {
        cpu_moe_forward_parallel(output, input, gate_weights,
                                expert_weights_1, expert_bias_1,
                                expert_weights_2, expert_bias_2,
                                batch_size, d_model, d_ff, num_experts, top_k, -1);
    } else {
        // Default to naive
        cpu_moe_forward(output, input, gate_weights,
                       expert_weights_1, expert_bias_1,
                       expert_weights_2, expert_bias_2,
                       batch_size, d_model, d_ff, num_experts, top_k);
    }

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<float, std::milli> duration = end - start;
    return duration.count();
}
