/**
 * @file test_layer_norm.cu
 * @brief Unit tests for Layer Normalization kernel
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/layer_norm.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <numeric>

using namespace llm;

/**
 * @brief Test fixture for LayerNorm tests with GPU setup
 */
class LayerNormTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test LayerNorm weight allocation and initialization
 */
TEST_F(LayerNormTest, WeightAllocation) {
    const int hidden_dim = 64;

    LayerNormWeights weights = allocate_layer_norm_weights(hidden_dim);

    // Verify gamma = 1.0
    std::vector<float> h_gamma(hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_gamma.data(), weights.gamma,
                          hidden_dim * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < hidden_dim; ++i) {
        EXPECT_FLOAT_EQ(h_gamma[i], 1.0f);
    }

    // Verify beta = 0.0
    std::vector<float> h_beta(hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_beta.data(), weights.beta,
                          hidden_dim * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < hidden_dim; ++i) {
        EXPECT_FLOAT_EQ(h_beta[i], 0.0f);
    }

    free_layer_norm_weights(weights);
}

/**
 * @brief Test LayerNorm produces approximately zero mean and unit variance
 *
 * With gamma=1.0 and beta=0.0, the output of LayerNorm should have
 * zero mean and unit variance for each row.
 */
TEST_F(LayerNormTest, ZeroMeanUnitVariance) {
    const int batch_size = 4;
    const int hidden_dim = 128;

    // Create input with non-trivial values
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i % 17) * 0.5f - 4.0f;
    }

    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    LayerNormWeights weights = allocate_layer_norm_weights(hidden_dim);

    // Run LayerNorm
    layer_norm_forward(d_output, d_input, weights.gamma, weights.beta,
                      batch_size, hidden_dim);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy output to host
    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify each row has approximately zero mean and unit variance
    for (int b = 0; b < batch_size; ++b) {
        float* row = h_output.data() + b * hidden_dim;

        // Compute mean
        float mean = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            mean += row[i];
        }
        mean /= hidden_dim;

        // Compute variance
        float var = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            float diff = row[i] - mean;
            var += diff * diff;
        }
        var /= hidden_dim;

        EXPECT_NEAR(mean, 0.0f, 1e-4f) << "Row " << b << " mean not zero";
        EXPECT_NEAR(var, 1.0f, 1e-2f) << "Row " << b << " variance not one";
    }

    free_layer_norm_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test LayerNorm with custom gamma and beta
 *
 * With gamma=2.0 and beta=1.0, output should have mean~=1.0 and std~=2.0.
 */
TEST_F(LayerNormTest, CustomGammaBeta) {
    const int batch_size = 2;
    const int hidden_dim = 64;

    // Create input
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i % 11) * 0.3f - 1.5f;
    }

    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    // Custom gamma = 2.0, beta = 1.0
    float* d_gamma = cuda_malloc<float>(hidden_dim);
    float* d_beta = cuda_malloc<float>(hidden_dim);
    std::vector<float> h_gamma(hidden_dim, 2.0f);
    std::vector<float> h_beta(hidden_dim, 1.0f);
    CHECK_CUDA(cudaMemcpy(d_gamma, h_gamma.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_beta, h_beta.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));

    // Run LayerNorm
    layer_norm_forward(d_output, d_input, d_gamma, d_beta,
                      batch_size, hidden_dim);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy output
    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify output: mean should be ~1.0 (beta), std should be ~2.0 (gamma)
    for (int b = 0; b < batch_size; ++b) {
        float* row = h_output.data() + b * hidden_dim;

        float mean = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) mean += row[i];
        mean /= hidden_dim;

        float var = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            float diff = row[i] - mean;
            var += diff * diff;
        }
        var /= hidden_dim;

        EXPECT_NEAR(mean, 1.0f, 1e-3f) << "Row " << b << " mean incorrect";
        EXPECT_NEAR(std::sqrt(var), 2.0f, 5e-2f) << "Row " << b << " std incorrect";
    }

    cuda_free(d_input);
    cuda_free(d_output);
    cuda_free(d_gamma);
    cuda_free(d_beta);
}

/**
 * @brief Test LayerNorm against CPU reference implementation
 */
TEST_F(LayerNormTest, MatchCPUReference) {
    const int batch_size = 3;
    const int hidden_dim = 32;
    const float eps = 1e-5f;

    // Create input
    std::vector<float> h_input(batch_size * hidden_dim);
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        h_input[i] = static_cast<float>(i) * 0.01f - 0.5f;
    }

    // CPU reference
    std::vector<float> h_expected(batch_size * hidden_dim);
    for (int b = 0; b < batch_size; ++b) {
        const float* row = h_input.data() + b * hidden_dim;
        float* out_row = h_expected.data() + b * hidden_dim;

        float mean = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) mean += row[i];
        mean /= hidden_dim;

        float var = 0.0f;
        for (int i = 0; i < hidden_dim; ++i) {
            float d = row[i] - mean;
            var += d * d;
        }
        var /= hidden_dim;

        float inv_std = 1.0f / std::sqrt(var + eps);
        for (int i = 0; i < hidden_dim; ++i) {
            out_row[i] = (row[i] - mean) * inv_std;  // gamma=1, beta=0
        }
    }

    // GPU computation
    float* d_input = cuda_malloc<float>(batch_size * hidden_dim);
    float* d_output = cuda_malloc<float>(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          h_input.size() * sizeof(float), cudaMemcpyHostToDevice));

    LayerNormWeights weights = allocate_layer_norm_weights(hidden_dim);
    layer_norm_forward(d_output, d_input, weights.gamma, weights.beta,
                      batch_size, hidden_dim, eps);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(batch_size * hidden_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          h_output.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Compare
    for (int i = 0; i < batch_size * hidden_dim; ++i) {
        EXPECT_NEAR(h_output[i], h_expected[i], 1e-4f) << "Mismatch at index " << i;
    }

    free_layer_norm_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test LayerNorm with single element rows
 */
TEST_F(LayerNormTest, SingleElementRow) {
    const int batch_size = 4;
    const int hidden_dim = 1;

    std::vector<float> h_input = {1.0f, 2.0f, 3.0f, 4.0f};
    float* d_input = cuda_malloc<float>(batch_size);
    float* d_output = cuda_malloc<float>(batch_size);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          batch_size * sizeof(float), cudaMemcpyHostToDevice));

    LayerNormWeights weights = allocate_layer_norm_weights(hidden_dim);
    layer_norm_forward(d_output, d_input, weights.gamma, weights.beta,
                      batch_size, hidden_dim);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(batch_size);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          batch_size * sizeof(float), cudaMemcpyDeviceToHost));

    // Single element: (x - x) / sqrt(0 + eps) = 0
    for (int i = 0; i < batch_size; ++i) {
        EXPECT_NEAR(h_output[i], 0.0f, 1e-5f);
    }

    free_layer_norm_weights(weights);
    cuda_free(d_input);
    cuda_free(d_output);
}
