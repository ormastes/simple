/**
 * @file test_feed_forward.cu
 * @brief Unit tests for Feed-Forward Network kernel
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/feed_forward.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for FFN tests with GPU setup
 */
class FeedForwardTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test FFN weight allocation
 */
TEST_F(FeedForwardTest, WeightAllocation) {
    FFNConfig config(64, 256);

    FFNWeights weights = allocate_ffn_weights(config);

    // Verify weights are allocated (non-null)
    EXPECT_NE(weights.W1, nullptr);
    EXPECT_NE(weights.b1, nullptr);
    EXPECT_NE(weights.W2, nullptr);
    EXPECT_NE(weights.b2, nullptr);

    // Verify biases are zero-initialized
    std::vector<float> h_b1(config.d_ff);
    CHECK_CUDA(cudaMemcpy(h_b1.data(), weights.b1,
                          config.d_ff * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < config.d_ff; ++i) {
        EXPECT_FLOAT_EQ(h_b1[i], 0.0f);
    }

    std::vector<float> h_b2(config.d_model);
    CHECK_CUDA(cudaMemcpy(h_b2.data(), weights.b2,
                          config.d_model * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < config.d_model; ++i) {
        EXPECT_FLOAT_EQ(h_b2[i], 0.0f);
    }

    free_ffn_weights(weights);
}

/**
 * @brief Test FFN forward produces correct output shape
 *
 * Output should have the same shape as input: [batch*seq, d_model]
 */
TEST_F(FeedForwardTest, OutputShape) {
    const int batch_size = 2;
    const int seq_len = 4;
    const int d_model = 32;
    const int d_ff = 128;

    FFNConfig config(d_model, d_ff);
    FFNWeights weights = allocate_ffn_weights(config);

    int total_tokens = batch_size * seq_len;

    // Create input
    std::vector<float> h_input(total_tokens * d_model, 0.1f);
    float* d_input = cuda_malloc<float>(total_tokens * d_model);
    float* d_output = cuda_malloc<float>(total_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    // Forward pass
    ffn_forward(d_output, d_input, weights, config, batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy output and verify it has the correct number of elements
    std::vector<float> h_output(total_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify all values are finite
    for (size_t i = 0; i < h_output.size(); ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i])) << "Non-finite at index " << i;
    }

    free_ffn_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test FFN produces non-trivial output
 *
 * With random weights, the output should not be all zeros (GELU preserves
 * positive values and slightly passes negative values).
 */
TEST_F(FeedForwardTest, NonTrivialOutput) {
    const int batch_size = 2;
    const int seq_len = 4;
    const int d_model = 32;
    const int d_ff = 128;

    FFNConfig config(d_model, d_ff);
    FFNWeights weights = allocate_ffn_weights(config);

    int total_tokens = batch_size * seq_len;

    // Create non-zero input
    std::vector<float> h_input(total_tokens * d_model);
    for (size_t i = 0; i < h_input.size(); ++i) {
        h_input[i] = static_cast<float>(i % 7) * 0.5f - 1.5f;
    }

    float* d_input = cuda_malloc<float>(total_tokens * d_model);
    float* d_output = cuda_malloc<float>(total_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    ffn_forward(d_output, d_input, weights, config, batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Output should be non-trivial (not all zeros)
    int non_zero_count = 0;
    for (float val : h_output) {
        if (std::abs(val) > 1e-6f) {
            non_zero_count++;
        }
    }
    EXPECT_GT(non_zero_count, static_cast<int>(h_output.size() / 2))
        << "Too many zero values in FFN output";

    free_ffn_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test GELU activation kernel directly
 *
 * GELU(0) should be 0, GELU(large positive) ~ x, GELU(large negative) ~ 0.
 */
TEST_F(FeedForwardTest, GELUActivation) {
    const int size = 5;
    std::vector<float> h_data = {0.0f, 1.0f, -1.0f, 3.0f, -3.0f};

    float* d_data = cuda_malloc<float>(size);
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(),
                          size * sizeof(float), cudaMemcpyHostToDevice));

    gelu_kernel<<<1, size>>>(d_data, size);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_result(size);
    CHECK_CUDA(cudaMemcpy(h_result.data(), d_data,
                          size * sizeof(float), cudaMemcpyDeviceToHost));

    // GELU(0) = 0
    EXPECT_NEAR(h_result[0], 0.0f, 1e-5f);

    // GELU(1) ~ 0.8413 (approximately)
    EXPECT_NEAR(h_result[1], 0.8413f, 0.01f);

    // GELU(-1) ~ -0.1587 (approximately)
    EXPECT_NEAR(h_result[2], -0.1587f, 0.01f);

    // GELU(3) ~ 3.0 (nearly identity for large positive)
    EXPECT_NEAR(h_result[3], 3.0f, 0.01f);

    // GELU(-3) ~ 0.0 (nearly zero for large negative)
    EXPECT_NEAR(h_result[4], 0.0f, 0.01f);

    cuda_free(d_data);
}

/**
 * @brief Test FFN with default d_ff = 4 * d_model
 */
TEST_F(FeedForwardTest, DefaultFFDimension) {
    const int d_model = 64;
    FFNConfig config(d_model);  // d_ff defaults to 4 * 64 = 256

    EXPECT_EQ(config.d_ff, 4 * d_model);

    FFNWeights weights = allocate_ffn_weights(config);

    // Verify we can do a forward pass with default config
    int total_tokens = 2;
    float* d_input = cuda_malloc<float>(total_tokens * d_model);
    float* d_output = cuda_malloc<float>(total_tokens * d_model);
    CHECK_CUDA(cudaMemset(d_input, 0, total_tokens * d_model * sizeof(float)));

    ffn_forward(d_output, d_input, weights, config, 1, 2);
    CHECK_CUDA(cudaDeviceSynchronize());

    free_ffn_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test FFN free sets pointers to null
 */
TEST_F(FeedForwardTest, FreeWeights) {
    FFNConfig config(32, 128);
    FFNWeights weights = allocate_ffn_weights(config);

    EXPECT_NE(weights.W1, nullptr);
    EXPECT_NE(weights.W2, nullptr);

    free_ffn_weights(weights);

    EXPECT_EQ(weights.W1, nullptr);
    EXPECT_EQ(weights.b1, nullptr);
    EXPECT_EQ(weights.W2, nullptr);
    EXPECT_EQ(weights.b2, nullptr);
}
