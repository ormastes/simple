/**
 * @file test_gradients.cu
 * @brief Unit tests for gradient clipping and accumulation GPU kernels
 *
 * Verifies gradient clipping by norm and gradient accumulation
 * correctness on GPU.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <vector>
#include <cmath>

// Forward declarations for gradient utilities (defined in gradient_kernels.cu)
namespace llm {
float gradient_clip_by_norm(float* d_grads, int num_params, float max_norm,
                            cudaStream_t stream);
void gradient_accumulate(float* d_accum, const float* d_grads,
                         int num_params, cudaStream_t stream);
void gradient_zero(float* d_grads, int num_params, cudaStream_t stream);
}

namespace llm {
namespace test {

/**
 * @brief Test fixture for gradient utility tests
 */
class GradientKernelTest : public ::testing::Test {
protected:
    void SetUp() override {
        cudaSetDevice(0);
    }
};

/// Gradient clipping should not modify gradients when norm is below threshold
TEST_F(GradientKernelTest, ClipNoOpWhenBelowThreshold) {
    const int N = 4;
    // Gradient vector [1, 0, 0, 0] has norm 1.0
    std::vector<float> h_grads = {1.0f, 0.0f, 0.0f, 0.0f};

    float* d_grads;
    cudaMalloc(&d_grads, N * sizeof(float));
    cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    // Max norm = 2.0, actual norm = 1.0 -> no clipping
    float norm = gradient_clip_by_norm(d_grads, N, 2.0f, 0);
    cudaDeviceSynchronize();

    EXPECT_NEAR(norm, 1.0f, 0.01f);

    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), d_grads, N * sizeof(float), cudaMemcpyDeviceToHost);

    // Should be unchanged
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_result[i], h_grads[i], 1e-5f);
    }

    cudaFree(d_grads);
}

/// Gradient clipping should scale down when norm exceeds threshold
TEST_F(GradientKernelTest, ClipScalesDownWhenAboveThreshold) {
    const int N = 4;
    // Gradient vector [3, 4, 0, 0] has norm 5.0
    std::vector<float> h_grads = {3.0f, 4.0f, 0.0f, 0.0f};

    float* d_grads;
    cudaMalloc(&d_grads, N * sizeof(float));
    cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    // Max norm = 1.0, actual norm = 5.0 -> scale by 1/5
    float norm = gradient_clip_by_norm(d_grads, N, 1.0f, 0);
    cudaDeviceSynchronize();

    EXPECT_NEAR(norm, 5.0f, 0.01f);

    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), d_grads, N * sizeof(float), cudaMemcpyDeviceToHost);

    // Should be scaled by max_norm / norm = 1/5
    EXPECT_NEAR(h_result[0], 0.6f, 0.01f);  // 3 * 0.2
    EXPECT_NEAR(h_result[1], 0.8f, 0.01f);  // 4 * 0.2

    // Verify new norm is approximately max_norm
    float new_norm = 0.0f;
    for (int i = 0; i < N; i++) {
        new_norm += h_result[i] * h_result[i];
    }
    new_norm = std::sqrt(new_norm);
    EXPECT_NEAR(new_norm, 1.0f, 0.01f);

    cudaFree(d_grads);
}

/// Gradient accumulation should add element-wise
TEST_F(GradientKernelTest, AccumulateAddsElementwise) {
    const int N = 4;
    std::vector<float> h_accum = {1.0f, 2.0f, 3.0f, 4.0f};
    std::vector<float> h_grads = {0.1f, 0.2f, 0.3f, 0.4f};

    float* d_accum;
    float* d_grads;
    cudaMalloc(&d_accum, N * sizeof(float));
    cudaMalloc(&d_grads, N * sizeof(float));
    cudaMemcpy(d_accum, h_accum.data(), N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    gradient_accumulate(d_accum, d_grads, N, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), d_accum, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_result[i], h_accum[i] + h_grads[i], 1e-5f);
    }

    cudaFree(d_accum);
    cudaFree(d_grads);
}

/// Gradient zero should clear buffer
TEST_F(GradientKernelTest, ZeroClearsBuffer) {
    const int N = 4;
    std::vector<float> h_grads = {1.0f, 2.0f, 3.0f, 4.0f};

    float* d_grads;
    cudaMalloc(&d_grads, N * sizeof(float));
    cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    gradient_zero(d_grads, N, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), d_grads, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_result[i], 0.0f);
    }

    cudaFree(d_grads);
}

/// Multiple accumulations should stack correctly
TEST_F(GradientKernelTest, MultipleAccumulations) {
    const int N = 2;
    std::vector<float> h_grads = {1.0f, 2.0f};

    float* d_accum;
    float* d_grads;
    cudaMalloc(&d_accum, N * sizeof(float));
    cudaMalloc(&d_grads, N * sizeof(float));

    // Start from zero
    gradient_zero(d_accum, N, 0);
    cudaMemcpy(d_grads, h_grads.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    // Accumulate 3 times
    gradient_accumulate(d_accum, d_grads, N, 0);
    gradient_accumulate(d_accum, d_grads, N, 0);
    gradient_accumulate(d_accum, d_grads, N, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_result(N);
    cudaMemcpy(h_result.data(), d_accum, N * sizeof(float), cudaMemcpyDeviceToHost);

    EXPECT_NEAR(h_result[0], 3.0f, 1e-5f);  // 1.0 * 3
    EXPECT_NEAR(h_result[1], 6.0f, 1e-5f);  // 2.0 * 3

    cudaFree(d_accum);
    cudaFree(d_grads);
}

} // namespace test
} // namespace llm
