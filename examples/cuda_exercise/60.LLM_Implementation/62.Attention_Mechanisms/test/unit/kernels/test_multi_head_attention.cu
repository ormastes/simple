/**
 * @file test_multi_head_attention.cu
 * @brief Unit tests for multi-head attention forward pass
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/multi_head_attention.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <random>

using namespace llm;

/**
 * @brief Test fixture for multi-head attention tests with GPU setup
 */
class MultiHeadAttentionTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test MHA forward produces correct output shape (non-zero, finite)
 */
TEST_F(MultiHeadAttentionTest, Forward_OutputShape) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 16;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    // Allocate and initialize weights
    AttentionWeights weights = allocate_attention_weights(config);
    initialize_attention_weights(weights, config, 42);

    int total_elements = batch_size * seq_len * d_model;

    // Create input
    std::vector<float> h_input(total_elements);
    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (auto& val : h_input) val = dist(gen);

    float* d_input = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Forward pass
    multi_head_attention_forward(d_output, d_input, weights, config,
                                batch_size, seq_len, true);

    // Copy output back
    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Check output shape: should have non-zero finite values
    int non_zero = 0;
    for (float val : h_output) {
        EXPECT_TRUE(std::isfinite(val)) << "Output contains non-finite value: " << val;
        if (std::abs(val) > 1e-8f) non_zero++;
    }
    EXPECT_GT(non_zero, 0) << "Output should contain non-zero values";

    cuda_free(d_input);
    cuda_free(d_output);
    free_attention_weights(weights);
}

/**
 * @brief Test MHA output changes with different weights
 */
TEST_F(MultiHeadAttentionTest, Forward_DifferentWeightsProduceDifferentOutput) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 16;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    // Same input for both runs
    std::vector<float> h_input(total_elements);
    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (auto& val : h_input) val = dist(gen);

    float* d_input = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Run 1: weights with seed 42
    AttentionWeights weights1 = allocate_attention_weights(config);
    initialize_attention_weights(weights1, config, 42);

    float* d_output1 = cuda_malloc<float>(total_elements);
    multi_head_attention_forward(d_output1, d_input, weights1, config,
                                batch_size, seq_len, true);

    std::vector<float> h_output1(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output1.data(), d_output1, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Run 2: weights with seed 123
    AttentionWeights weights2 = allocate_attention_weights(config);
    initialize_attention_weights(weights2, config, 123);

    float* d_output2 = cuda_malloc<float>(total_elements);
    multi_head_attention_forward(d_output2, d_input, weights2, config,
                                batch_size, seq_len, true);

    std::vector<float> h_output2(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output2.data(), d_output2, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Outputs should differ
    int diff_count = 0;
    for (int i = 0; i < total_elements; ++i) {
        if (std::abs(h_output1[i] - h_output2[i]) > 1e-5f) {
            diff_count++;
        }
    }
    EXPECT_GT(diff_count, total_elements / 2)
        << "Different weights should produce different outputs";

    cuda_free(d_input);
    cuda_free(d_output1);
    cuda_free(d_output2);
    free_attention_weights(weights1);
    free_attention_weights(weights2);
}

/**
 * @brief Test MHA with causal vs non-causal produces different results
 */
TEST_F(MultiHeadAttentionTest, Forward_CausalVsNonCausal) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 16;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_input(total_elements);
    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (auto& val : h_input) val = dist(gen);

    float* d_input = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    AttentionWeights weights = allocate_attention_weights(config);
    initialize_attention_weights(weights, config, 42);

    // Causal forward
    float* d_causal_out = cuda_malloc<float>(total_elements);
    multi_head_attention_forward(d_causal_out, d_input, weights, config,
                                batch_size, seq_len, /*causal=*/true);

    std::vector<float> h_causal(total_elements);
    CHECK_CUDA(cudaMemcpy(h_causal.data(), d_causal_out, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Non-causal forward
    float* d_noncausal_out = cuda_malloc<float>(total_elements);
    multi_head_attention_forward(d_noncausal_out, d_input, weights, config,
                                batch_size, seq_len, /*causal=*/false);

    std::vector<float> h_noncausal(total_elements);
    CHECK_CUDA(cudaMemcpy(h_noncausal.data(), d_noncausal_out, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // The first token (position 0) can only attend to itself in both cases,
    // so it should produce the same output.
    // But later tokens should differ because causal masking changes the attention.
    int diff_count = 0;
    for (int i = 0; i < total_elements; ++i) {
        if (std::abs(h_causal[i] - h_noncausal[i]) > 1e-4f) {
            diff_count++;
        }
    }
    // At least some elements should differ (tokens > 0 see different contexts)
    EXPECT_GT(diff_count, 0)
        << "Causal and non-causal attention should produce different outputs for seq_len > 1";

    cuda_free(d_input);
    cuda_free(d_causal_out);
    cuda_free(d_noncausal_out);
    free_attention_weights(weights);
}

/**
 * @brief Test MHA with batched input
 */
TEST_F(MultiHeadAttentionTest, Forward_BatchProcessing) {
    int batch_size = 2;
    int seq_len = 4;
    int d_model = 16;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_input(total_elements);
    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (auto& val : h_input) val = dist(gen);

    float* d_input = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    AttentionWeights weights = allocate_attention_weights(config);
    initialize_attention_weights(weights, config, 42);

    multi_head_attention_forward(d_output, d_input, weights, config,
                                batch_size, seq_len, true);

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // All values should be finite
    for (int i = 0; i < total_elements; ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i]))
            << "Output[" << i << "] = " << h_output[i] << " is not finite";
    }

    // Batch 0 and Batch 1 should produce different outputs (different inputs)
    int per_batch = seq_len * d_model;
    int diff_count = 0;
    for (int i = 0; i < per_batch; ++i) {
        if (std::abs(h_output[i] - h_output[per_batch + i]) > 1e-5f) {
            diff_count++;
        }
    }
    EXPECT_GT(diff_count, per_batch / 2)
        << "Different batch inputs should produce different outputs";

    cuda_free(d_input);
    cuda_free(d_output);
    free_attention_weights(weights);
}

/**
 * @brief Test MHA determinism: same input + weights = same output
 */
TEST_F(MultiHeadAttentionTest, Forward_Deterministic) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 16;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_input(total_elements);
    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (auto& val : h_input) val = dist(gen);

    float* d_input = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    AttentionWeights weights = allocate_attention_weights(config);
    initialize_attention_weights(weights, config, 42);

    // Run twice
    float* d_output1 = cuda_malloc<float>(total_elements);
    float* d_output2 = cuda_malloc<float>(total_elements);

    multi_head_attention_forward(d_output1, d_input, weights, config,
                                batch_size, seq_len, true);
    multi_head_attention_forward(d_output2, d_input, weights, config,
                                batch_size, seq_len, true);

    std::vector<float> h_out1(total_elements), h_out2(total_elements);
    CHECK_CUDA(cudaMemcpy(h_out1.data(), d_output1, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_out2.data(), d_output2, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int i = 0; i < total_elements; ++i) {
        EXPECT_FLOAT_EQ(h_out1[i], h_out2[i])
            << "Non-deterministic output at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output1);
    cuda_free(d_output2);
    free_attention_weights(weights);
}
