/**
 * @file test_attention_setup.cu
 * @brief Unit tests for attention weight allocation, initialization, and cleanup
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/multi_head_attention.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for attention setup tests with GPU
 */
class AttentionSetupTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test AttentionConfig construction with default parameters
 */
TEST_F(AttentionSetupTest, Config_DefaultConstruction) {
    AttentionConfig config(768, 12);

    EXPECT_EQ(config.d_model, 768);
    EXPECT_EQ(config.num_heads, 12);
    EXPECT_EQ(config.head_dim, 64);  // 768 / 12
    EXPECT_EQ(config.max_seq_len, 1024);
    EXPECT_FLOAT_EQ(config.dropout, 0.0f);
}

/**
 * @brief Test AttentionConfig construction with custom parameters
 */
TEST_F(AttentionSetupTest, Config_CustomConstruction) {
    AttentionConfig config(512, 8, 2048, 0.1f);

    EXPECT_EQ(config.d_model, 512);
    EXPECT_EQ(config.num_heads, 8);
    EXPECT_EQ(config.head_dim, 64);  // 512 / 8
    EXPECT_EQ(config.max_seq_len, 2048);
    EXPECT_FLOAT_EQ(config.dropout, 0.1f);
}

/**
 * @brief Test attention weight allocation and freeing
 */
TEST_F(AttentionSetupTest, AllocateAndFreeWeights) {
    AttentionConfig config(64, 4);

    AttentionWeights weights = allocate_attention_weights(config);

    // All pointers should be non-null after allocation
    EXPECT_NE(weights.W_Q, nullptr);
    EXPECT_NE(weights.W_K, nullptr);
    EXPECT_NE(weights.W_V, nullptr);
    EXPECT_NE(weights.W_O, nullptr);
    EXPECT_NE(weights.b_Q, nullptr);
    EXPECT_NE(weights.b_K, nullptr);
    EXPECT_NE(weights.b_V, nullptr);
    EXPECT_NE(weights.b_O, nullptr);

    // Free should not crash
    free_attention_weights(weights);

    // After free, all pointers should be null
    EXPECT_EQ(weights.W_Q, nullptr);
    EXPECT_EQ(weights.W_K, nullptr);
    EXPECT_EQ(weights.W_V, nullptr);
    EXPECT_EQ(weights.W_O, nullptr);
    EXPECT_EQ(weights.b_Q, nullptr);
    EXPECT_EQ(weights.b_K, nullptr);
    EXPECT_EQ(weights.b_V, nullptr);
    EXPECT_EQ(weights.b_O, nullptr);
}

/**
 * @brief Test double free safety (pointers set to null)
 */
TEST_F(AttentionSetupTest, DoubleFree_Safe) {
    AttentionConfig config(32, 2);

    AttentionWeights weights = allocate_attention_weights(config);
    free_attention_weights(weights);

    // Second free should be safe (all pointers are null)
    free_attention_weights(weights);
}

/**
 * @brief Test Xavier initialization produces reasonable weight distributions
 */
TEST_F(AttentionSetupTest, InitializeWeights_XavierDistribution) {
    int d_model = 64;
    AttentionConfig config(d_model, 4);

    AttentionWeights weights = allocate_attention_weights(config);
    initialize_attention_weights(weights, config, 42);

    // Read back W_Q weights to host
    int matrix_size = d_model * d_model;
    std::vector<float> h_W_Q(matrix_size);
    CHECK_CUDA(cudaMemcpy(h_W_Q.data(), weights.W_Q,
                         matrix_size * sizeof(float),
                         cudaMemcpyDeviceToHost));

    // Compute mean and stddev
    double sum = 0.0;
    for (float val : h_W_Q) {
        sum += val;
    }
    double mean = sum / matrix_size;

    double var_sum = 0.0;
    for (float val : h_W_Q) {
        double diff = val - mean;
        var_sum += diff * diff;
    }
    double stddev = std::sqrt(var_sum / matrix_size);

    // Mean should be near 0 (within tolerance for random initialization)
    EXPECT_NEAR(mean, 0.0, 0.05);

    // Stddev should be approximately 1/sqrt(d_model) = 1/8 = 0.125
    float expected_stddev = 1.0f / std::sqrt(static_cast<float>(d_model));
    EXPECT_NEAR(stddev, expected_stddev, 0.03);

    // Biases should be zero
    std::vector<float> h_bias(d_model);
    CHECK_CUDA(cudaMemcpy(h_bias.data(), weights.b_Q,
                         d_model * sizeof(float),
                         cudaMemcpyDeviceToHost));

    for (int i = 0; i < d_model; ++i) {
        EXPECT_FLOAT_EQ(h_bias[i], 0.0f);
    }

    free_attention_weights(weights);
}

/**
 * @brief Test that different seeds produce different weights
 */
TEST_F(AttentionSetupTest, InitializeWeights_DifferentSeeds) {
    int d_model = 32;
    AttentionConfig config(d_model, 2);

    AttentionWeights weights1 = allocate_attention_weights(config);
    AttentionWeights weights2 = allocate_attention_weights(config);

    initialize_attention_weights(weights1, config, 42);
    initialize_attention_weights(weights2, config, 123);

    // Read back both W_Q matrices
    int matrix_size = d_model * d_model;
    std::vector<float> h_W1(matrix_size), h_W2(matrix_size);
    CHECK_CUDA(cudaMemcpy(h_W1.data(), weights1.W_Q,
                         matrix_size * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_W2.data(), weights2.W_Q,
                         matrix_size * sizeof(float), cudaMemcpyDeviceToHost));

    // At least some values should differ
    int diff_count = 0;
    for (int i = 0; i < matrix_size; ++i) {
        if (std::abs(h_W1[i] - h_W2[i]) > 1e-6f) {
            diff_count++;
        }
    }
    EXPECT_GT(diff_count, matrix_size / 2);

    free_attention_weights(weights1);
    free_attention_weights(weights2);
}

/**
 * @brief Test allocation with larger model dimensions
 */
TEST_F(AttentionSetupTest, AllocateWeights_LargerModel) {
    AttentionConfig config(256, 8);

    AttentionWeights weights = allocate_attention_weights(config);

    // Should succeed without CUDA errors
    CHECK_CUDA(cudaDeviceSynchronize());

    EXPECT_NE(weights.W_Q, nullptr);
    EXPECT_NE(weights.W_O, nullptr);

    free_attention_weights(weights);
}
