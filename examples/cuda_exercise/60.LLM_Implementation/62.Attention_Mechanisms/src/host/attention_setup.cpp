/**
 * @file attention_setup.cpp
 * @brief Host-side setup for attention weights: allocation, initialization, and cleanup
 *
 * Provides utility functions for managing attention weight matrices on the GPU,
 * including Xavier/Glorot initialization for stable training.
 */

#include "common/multi_head_attention.h"
#include "cuda_utils.h"
#include <vector>
#include <random>
#include <cmath>
#include <cstring>

namespace llm {

AttentionWeights allocate_attention_weights(const AttentionConfig& config) {
    AttentionWeights weights;
    int d = config.d_model;

    // Allocate weight matrices [d_model, d_model]
    size_t matrix_bytes = d * d * sizeof(float);
    CHECK_CUDA(cudaMalloc(&weights.W_Q, matrix_bytes));
    CHECK_CUDA(cudaMalloc(&weights.W_K, matrix_bytes));
    CHECK_CUDA(cudaMalloc(&weights.W_V, matrix_bytes));
    CHECK_CUDA(cudaMalloc(&weights.W_O, matrix_bytes));

    // Allocate bias vectors [d_model]
    size_t bias_bytes = d * sizeof(float);
    CHECK_CUDA(cudaMalloc(&weights.b_Q, bias_bytes));
    CHECK_CUDA(cudaMalloc(&weights.b_K, bias_bytes));
    CHECK_CUDA(cudaMalloc(&weights.b_V, bias_bytes));
    CHECK_CUDA(cudaMalloc(&weights.b_O, bias_bytes));

    return weights;
}

void free_attention_weights(AttentionWeights& weights) {
    if (weights.W_Q) { cudaFree(weights.W_Q); weights.W_Q = nullptr; }
    if (weights.W_K) { cudaFree(weights.W_K); weights.W_K = nullptr; }
    if (weights.W_V) { cudaFree(weights.W_V); weights.W_V = nullptr; }
    if (weights.W_O) { cudaFree(weights.W_O); weights.W_O = nullptr; }
    if (weights.b_Q) { cudaFree(weights.b_Q); weights.b_Q = nullptr; }
    if (weights.b_K) { cudaFree(weights.b_K); weights.b_K = nullptr; }
    if (weights.b_V) { cudaFree(weights.b_V); weights.b_V = nullptr; }
    if (weights.b_O) { cudaFree(weights.b_O); weights.b_O = nullptr; }
}

void initialize_attention_weights(AttentionWeights& weights,
                                  const AttentionConfig& config,
                                  unsigned int seed) {
    int d = config.d_model;
    size_t matrix_size = d * d;
    size_t bias_size = d;

    // Xavier/Glorot initialization: N(0, sqrt(2 / (fan_in + fan_out)))
    // For square weight matrices: N(0, sqrt(2 / (d + d))) = N(0, 1/sqrt(d))
    float stddev = 1.0f / std::sqrt(static_cast<float>(d));

    std::default_random_engine gen(seed);
    std::normal_distribution<float> dist(0.0f, stddev);

    // Initialize weight matrices
    auto init_matrix = [&](float* d_ptr) {
        std::vector<float> h_data(matrix_size);
        for (auto& val : h_data) {
            val = dist(gen);
        }
        CHECK_CUDA(cudaMemcpy(d_ptr, h_data.data(),
                              matrix_size * sizeof(float),
                              cudaMemcpyHostToDevice));
    };

    init_matrix(weights.W_Q);
    init_matrix(weights.W_K);
    init_matrix(weights.W_V);
    init_matrix(weights.W_O);

    // Initialize biases to zero
    std::vector<float> zeros(bias_size, 0.0f);
    CHECK_CUDA(cudaMemcpy(weights.b_Q, zeros.data(), bias_size * sizeof(float),
                          cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(weights.b_K, zeros.data(), bias_size * sizeof(float),
                          cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(weights.b_V, zeros.data(), bias_size * sizeof(float),
                          cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(weights.b_O, zeros.data(), bias_size * sizeof(float),
                          cudaMemcpyHostToDevice));
}

} // namespace llm
