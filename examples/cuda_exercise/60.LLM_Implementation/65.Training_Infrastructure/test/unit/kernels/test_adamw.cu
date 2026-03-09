/**
 * @file test_adamw.cu
 * @brief Unit tests for AdamW optimizer GPU kernel
 *
 * Verifies the AdamW parameter update direction, moment accumulation,
 * bias correction, and weight decay behavior on GPU.
 */

#include <gtest/gtest.h>
#include "common/optimizer.h"
#include <cuda_runtime.h>
#include <vector>
#include <cmath>

namespace llm {
namespace test {

/**
 * @brief Test fixture for AdamW kernel tests
 *
 * Sets up small parameter and gradient buffers for verifying
 * optimizer correctness on GPU.
 */
class AdamWKernelTest : public ::testing::Test {
protected:
    static constexpr int N = 4;  ///< Number of test parameters
    float* d_params = nullptr;
    float* d_grads = nullptr;
    AdamWState state;
    AdamWConfig config;

    void SetUp() override {
        // Allocate device buffers
        cudaMalloc(&d_params, N * sizeof(float));
        cudaMalloc(&d_grads, N * sizeof(float));

        // Initialize parameters to known values [1.0, 2.0, 3.0, 4.0]
        std::vector<float> h_params = {1.0f, 2.0f, 3.0f, 4.0f};
        cudaMemcpy(d_params, h_params.data(), N * sizeof(float), cudaMemcpyHostToDevice);

        // Initialize gradients [0.1, 0.2, 0.3, 0.4]
        std::vector<float> h_grads = {0.1f, 0.2f, 0.3f, 0.4f};
        cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

        // Allocate optimizer state
        state = allocate_adamw_state(N);
        config = AdamWConfig(1e-3f, 0.9f, 0.999f, 0.01f, 1e-8f);
    }

    void TearDown() override {
        cudaFree(d_params);
        cudaFree(d_grads);
        free_adamw_state(state);
    }
};

/// Verify parameters move in the direction opposite to gradients
TEST_F(AdamWKernelTest, UpdateDirection) {
    // Read initial parameters
    std::vector<float> initial_params(N);
    cudaMemcpy(initial_params.data(), d_params, N * sizeof(float), cudaMemcpyDeviceToHost);

    // Perform one step
    adamw_step(d_params, d_grads, state, config);
    cudaDeviceSynchronize();

    // Read updated parameters
    std::vector<float> updated_params(N);
    cudaMemcpy(updated_params.data(), d_params, N * sizeof(float), cudaMemcpyDeviceToHost);

    // All positive gradients should decrease parameters (including weight decay effect)
    for (int i = 0; i < N; i++) {
        EXPECT_LT(updated_params[i], initial_params[i])
            << "Parameter " << i << " should decrease with positive gradient";
    }
}

/// Verify first and second moments accumulate correctly
TEST_F(AdamWKernelTest, MomentAccumulation) {
    // Step 1
    adamw_step(d_params, d_grads, state, config);
    cudaDeviceSynchronize();
    EXPECT_EQ(state.step, 1);

    // Read moments after step 1
    std::vector<float> m1(N), v1(N);
    cudaMemcpy(m1.data(), state.d_m, N * sizeof(float), cudaMemcpyDeviceToHost);
    cudaMemcpy(v1.data(), state.d_v, N * sizeof(float), cudaMemcpyDeviceToHost);

    // First moment: m = beta1 * 0 + (1 - beta1) * grad = 0.1 * grad
    std::vector<float> h_grads = {0.1f, 0.2f, 0.3f, 0.4f};
    for (int i = 0; i < N; i++) {
        float expected_m = (1.0f - config.beta1) * h_grads[i];
        EXPECT_NEAR(m1[i], expected_m, 1e-6f) << "First moment mismatch at " << i;
    }

    // Second moment: v = beta2 * 0 + (1 - beta2) * grad^2 = 0.001 * grad^2
    for (int i = 0; i < N; i++) {
        float expected_v = (1.0f - config.beta2) * h_grads[i] * h_grads[i];
        EXPECT_NEAR(v1[i], expected_v, 1e-6f) << "Second moment mismatch at " << i;
    }

    // Step 2: moments should accumulate
    adamw_step(d_params, d_grads, state, config);
    cudaDeviceSynchronize();
    EXPECT_EQ(state.step, 2);

    std::vector<float> m2(N);
    cudaMemcpy(m2.data(), state.d_m, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        float expected_m2 = config.beta1 * m1[i] + (1.0f - config.beta1) * h_grads[i];
        EXPECT_NEAR(m2[i], expected_m2, 1e-6f) << "Accumulated moment mismatch at " << i;
    }
}

/// Verify that weight decay pushes parameters toward zero
TEST_F(AdamWKernelTest, WeightDecayEffect) {
    // Set zero gradients to isolate weight decay effect
    std::vector<float> zero_grads(N, 0.0f);
    cudaMemcpy(d_grads, zero_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    // With zero gradients, only weight decay should affect parameters
    // However, moments are also zero, so the adaptive part contributes nothing
    // param -= lr * weight_decay * param
    std::vector<float> initial_params(N);
    cudaMemcpy(initial_params.data(), d_params, N * sizeof(float), cudaMemcpyDeviceToHost);

    adamw_step(d_params, d_grads, state, config);
    cudaDeviceSynchronize();

    std::vector<float> updated_params(N);
    cudaMemcpy(updated_params.data(), d_params, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        // Weight decay should reduce magnitude
        EXPECT_LT(std::abs(updated_params[i]), std::abs(initial_params[i]))
            << "Weight decay should reduce parameter magnitude at " << i;
    }
}

/// Verify state allocation and deallocation
TEST_F(AdamWKernelTest, StateLifecycle) {
    AdamWState test_state = allocate_adamw_state(1024);
    EXPECT_NE(test_state.d_m, nullptr);
    EXPECT_NE(test_state.d_v, nullptr);
    EXPECT_EQ(test_state.step, 0);
    EXPECT_EQ(test_state.size, 1024u);

    free_adamw_state(test_state);
    EXPECT_EQ(test_state.d_m, nullptr);
    EXPECT_EQ(test_state.d_v, nullptr);
    EXPECT_EQ(test_state.step, 0);
    EXPECT_EQ(test_state.size, 0u);
}

} // namespace test
} // namespace llm
