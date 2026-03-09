/**
 * @file deepseek_loader.cpp
 * @brief Host-side DeepSeek R1 checkpoint loading
 *
 * Provides utilities for loading DeepSeek R1 model weights from binary
 * checkpoint files and mapping them to the internal weight structures
 * (GQAWeights, SwiGLUWeights, etc.).
 */

#include "common/deepseek_config.h"
#include "common/gqa_attention.h"
#include "common/swiglu_ffn.h"
#include "cuda_utils.h"
#include <vector>
#include <random>
#include <cmath>
#include <cstring>

namespace llm {

// --- GQA weight management ---

GQAWeights allocate_gqa_weights(const DeepSeekConfig& config) {
    GQAWeights weights{};
    int d = config.d_model;
    int head_dim = d / config.num_heads;
    int q_dim = config.num_heads * head_dim;    // = d_model
    int kv_dim = config.num_kv_heads * head_dim;

    // Query: [d_model, q_dim]
    CHECK_CUDA(cudaMalloc(&weights.W_Q, d * q_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_Q, q_dim * sizeof(float)));

    // Key/Value: [d_model, kv_dim] (smaller than Q due to GQA)
    CHECK_CUDA(cudaMalloc(&weights.W_K, d * kv_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_K, kv_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.W_V, d * kv_dim * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_V, kv_dim * sizeof(float)));

    // Output: [q_dim, d_model]
    CHECK_CUDA(cudaMalloc(&weights.W_O, q_dim * d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_O, d * sizeof(float)));

    return weights;
}

void free_gqa_weights(GQAWeights& weights) {
    if (weights.W_Q) { cudaFree(weights.W_Q); weights.W_Q = nullptr; }
    if (weights.W_K) { cudaFree(weights.W_K); weights.W_K = nullptr; }
    if (weights.W_V) { cudaFree(weights.W_V); weights.W_V = nullptr; }
    if (weights.W_O) { cudaFree(weights.W_O); weights.W_O = nullptr; }
    if (weights.b_Q) { cudaFree(weights.b_Q); weights.b_Q = nullptr; }
    if (weights.b_K) { cudaFree(weights.b_K); weights.b_K = nullptr; }
    if (weights.b_V) { cudaFree(weights.b_V); weights.b_V = nullptr; }
    if (weights.b_O) { cudaFree(weights.b_O); weights.b_O = nullptr; }
}

void initialize_gqa_weights(GQAWeights& weights,
                            const DeepSeekConfig& config,
                            unsigned int seed) {
    int d = config.d_model;
    int head_dim = d / config.num_heads;
    int q_dim = config.num_heads * head_dim;
    int kv_dim = config.num_kv_heads * head_dim;

    std::default_random_engine gen(seed);

    // Xavier init helper
    auto init_matrix = [&](float* d_ptr, int rows, int cols) {
        float stddev = 1.0f / std::sqrt(static_cast<float>(rows + cols));
        std::normal_distribution<float> dist(0.0f, stddev);
        std::vector<float> h_data(rows * cols);
        for (auto& val : h_data) val = dist(gen);
        CHECK_CUDA(cudaMemcpy(d_ptr, h_data.data(),
                              h_data.size() * sizeof(float),
                              cudaMemcpyHostToDevice));
    };

    auto init_zeros = [](float* d_ptr, int size) {
        CHECK_CUDA(cudaMemset(d_ptr, 0, size * sizeof(float)));
    };

    init_matrix(weights.W_Q, d, q_dim);
    init_matrix(weights.W_K, d, kv_dim);
    init_matrix(weights.W_V, d, kv_dim);
    init_matrix(weights.W_O, q_dim, d);

    init_zeros(weights.b_Q, q_dim);
    init_zeros(weights.b_K, kv_dim);
    init_zeros(weights.b_V, kv_dim);
    init_zeros(weights.b_O, d);
}

// --- SwiGLU weight management ---

SwiGLUWeights allocate_swiglu_weights(int d_model, int d_ff) {
    SwiGLUWeights weights{};

    CHECK_CUDA(cudaMalloc(&weights.W_gate, d_model * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.W_up,   d_model * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.W_down,  d_ff * d_model * sizeof(float)));

    CHECK_CUDA(cudaMalloc(&weights.b_gate, d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_up,   d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&weights.b_down,  d_model * sizeof(float)));

    return weights;
}

void free_swiglu_weights(SwiGLUWeights& weights) {
    if (weights.W_gate) { cudaFree(weights.W_gate); weights.W_gate = nullptr; }
    if (weights.W_up)   { cudaFree(weights.W_up);   weights.W_up = nullptr; }
    if (weights.W_down) { cudaFree(weights.W_down); weights.W_down = nullptr; }
    if (weights.b_gate) { cudaFree(weights.b_gate); weights.b_gate = nullptr; }
    if (weights.b_up)   { cudaFree(weights.b_up);   weights.b_up = nullptr; }
    if (weights.b_down) { cudaFree(weights.b_down); weights.b_down = nullptr; }
}

void initialize_swiglu_weights(SwiGLUWeights& weights,
                               int d_model, int d_ff,
                               unsigned int seed) {
    std::default_random_engine gen(seed);

    auto init_matrix = [&](float* d_ptr, int rows, int cols) {
        float stddev = 1.0f / std::sqrt(static_cast<float>(rows + cols));
        std::normal_distribution<float> dist(0.0f, stddev);
        std::vector<float> h_data(rows * cols);
        for (auto& val : h_data) val = dist(gen);
        CHECK_CUDA(cudaMemcpy(d_ptr, h_data.data(),
                              h_data.size() * sizeof(float),
                              cudaMemcpyHostToDevice));
    };

    auto init_zeros = [](float* d_ptr, int size) {
        CHECK_CUDA(cudaMemset(d_ptr, 0, size * sizeof(float)));
    };

    init_matrix(weights.W_gate, d_model, d_ff);
    init_matrix(weights.W_up,   d_model, d_ff);
    init_matrix(weights.W_down,  d_ff, d_model);

    init_zeros(weights.b_gate, d_ff);
    init_zeros(weights.b_up,   d_ff);
    init_zeros(weights.b_down, d_model);
}

} // namespace llm
