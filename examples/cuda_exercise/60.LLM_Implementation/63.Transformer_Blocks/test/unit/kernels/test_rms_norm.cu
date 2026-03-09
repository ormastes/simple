/**
 * @file test_rms_norm.cu
 * @brief Unit tests for RMS Normalization kernel
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/rms_norm.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for RMSNorm tests with GPU setup
 */
class RMSNormTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test RMSNorm weight allocation
 */
TEST_F(RMSNormTest, WeightAllocation) {
    const int hidden_dim = 64;

    float* weight = allocate_rms_norm_weights(hidden_dim);

    // Verify weight = 1.0
    std::vector<float> h_weight(hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_weight.data(), weight,
                          hidden_dim * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < hidden_dim; ++i) {
        EXPECT_FLOAT_EQ(h_weight[i], 1.0f);
    }

    free_rms_norm_weights(weight);
}

/**
 * @brief Test RMSNorm against CPU reference implementation
 *
 * CPU reference: output = weight * input * rsqrt(mean(input^2) + eps)
 */
TEST_F(RMSNormTest, MatchCPUReference) {
    const int batch_size = 4;
    const int hidden_dim = 64;
    const float eps = 1e-6f;

    // Create input with non-trivial values
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i % 13) * 0.3f - 1.8f;
    }

    // CPU reference
    std::vector<float> h_expected(batch_size * hidden_dim);
    for (int b = 0; b < batch_size; ++b) {
        const float* row = h_input.data() + b * hidden_dim;
        float* out_row = h_expected.data() + b * hidden_dim;

        // Compute sum of squares
        float sum_sq = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            sum_sq += row[i] * row[i];
        }
        float rms_inv = 1.0f / std::sqrt(sum_sq / hidden_dim + eps);

        // weight=1.0, so output = input * rms_inv
        for (int i = 0; i < hidden_dim; ++i) {
            out_row[i] = row[i] * rms_inv;
        }
    }

    // GPU computation
    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    float* d_weight = allocate_rms_norm_weights(hidden_dim);
    rms_norm_forward(d_output, d_input, d_weight,
                    batch_size, hidden_dim, eps);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Compare
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        EXPECT_NEAR(h_output[i], h_expected[i], 1e-4f) << "Mismatch at index " << i;
    }

    free_rms_norm_weights(d_weight);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test RMSNorm preserves scale direction
 *
 * After RMSNorm with weight=1, the RMS of the output should be approximately 1.
 */
TEST_F(RMSNormTest, OutputRMSNearOne) {
    const int batch_size = 3;
    const int hidden_dim = 128;

    // Create input
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i % 7) * 2.0f - 6.0f;
    }

    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    float* d_weight = allocate_rms_norm_weights(hidden_dim);
    rms_norm_forward(d_output, d_input, d_weight,
                    batch_size, hidden_dim);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify each row has RMS approximately 1.0
    for (int b = 0; b < batch_size; ++b) {
        float* row = h_output.data() + b * hidden_dim;
        float sum_sq = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            sum_sq += row[i] * row[i];
        }
        float rms = std::sqrt(sum_sq / hidden_dim);
        EXPECT_NEAR(rms, 1.0f, 1e-3f) << "Row " << b << " RMS not ~1.0";
    }

    free_rms_norm_weights(d_weight);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test RMSNorm with custom weights
 */
TEST_F(RMSNormTest, CustomWeights) {
    const int batch_size = 2;
    const int hidden_dim = 32;
    const float eps = 1e-6f;

    // Create input
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = 1.0f;  // uniform input
    }

    // Custom weight = 2.0
    std::vector<float> h_weight(hidden_dim, 2.0f);

    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_weight = cuda_malloc<float>(hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_weight, h_weight.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));

    rms_norm_forward(d_output, d_input, d_weight,
                    batch_size, hidden_dim, eps);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // For uniform input of 1.0: rms = 1.0, so output = weight * 1.0 * (1/1.0) = 2.0
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        EXPECT_NEAR(h_output[i], 2.0f, 1e-4f) << "Mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    cuda_free(d_weight);
}

/**
 * @brief Test RMSNorm with large hidden dimension
 */
TEST_F(RMSNormTest, LargeHiddenDim) {
    const int batch_size = 2;
    const int hidden_dim = 2048;  // Typical for larger models

    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i % 19) * 0.1f - 0.9f;
    }

    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    float* d_weight = allocate_rms_norm_weights(hidden_dim);
    rms_norm_forward(d_output, d_input, d_weight,
                    batch_size, hidden_dim);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Just verify no CUDA errors and output is finite
    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i])) << "Non-finite at index " << i;
    }

    free_rms_norm_weights(d_weight);
    cuda_free(d_input);
    cuda_free(d_output);
}
