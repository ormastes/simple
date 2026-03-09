/**
 * @file test_bias_residual.cu
 * @brief Unit tests for fused bias + residual addition kernel
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/bias_residual.cuh"
#include <vector>
#include <cstdlib>
#include <cmath>

// ---------------------------------------------------------------------------
// CPU reference implementation
// ---------------------------------------------------------------------------

static void cpu_bias_residual(float* output, const float* input,
                               const float* bias, const float* residual,
                               int rows, int cols) {
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int idx = r * cols + c;
            output[idx] = input[idx] + bias[c] + residual[idx];
        }
    }
}

static void fill_random(std::vector<float>& v, float lo = -1.0f, float hi = 1.0f) {
    for (auto& x : v) {
        x = lo + static_cast<float>(rand()) / RAND_MAX * (hi - lo);
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class BiasResidualTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
        srand(42);
    }

    float* to_device(const std::vector<float>& h_data) {
        float* d_ptr = nullptr;
        cudaMalloc(&d_ptr, h_data.size() * sizeof(float));
        cudaMemcpy(d_ptr, h_data.data(), h_data.size() * sizeof(float),
                   cudaMemcpyHostToDevice);
        return d_ptr;
    }

    std::vector<float> to_host(const float* d_ptr, int n) {
        std::vector<float> h_data(n);
        cudaMemcpy(h_data.data(), d_ptr, n * sizeof(float), cudaMemcpyDeviceToHost);
        return h_data;
    }
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

TEST_F(BiasResidualTest, Small_4x8) {
    const int rows = 4, cols = 8;
    std::vector<float> h_input(rows * cols), h_bias(cols), h_residual(rows * cols);
    std::vector<float> h_ref(rows * cols);
    fill_random(h_input);
    fill_random(h_bias);
    fill_random(h_residual);

    cpu_bias_residual(h_ref.data(), h_input.data(), h_bias.data(),
                      h_residual.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_bias = to_device(h_bias);
    float* d_residual = to_device(h_residual);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_bias_residual(d_output, d_input, d_bias, d_residual, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_bias); cudaFree(d_residual); cudaFree(d_output);
}

TEST_F(BiasResidualTest, Medium_32x256) {
    const int rows = 32, cols = 256;
    std::vector<float> h_input(rows * cols), h_bias(cols), h_residual(rows * cols);
    std::vector<float> h_ref(rows * cols);
    fill_random(h_input);
    fill_random(h_bias);
    fill_random(h_residual);

    cpu_bias_residual(h_ref.data(), h_input.data(), h_bias.data(),
                      h_residual.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_bias = to_device(h_bias);
    float* d_residual = to_device(h_residual);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_bias_residual(d_output, d_input, d_bias, d_residual, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_bias); cudaFree(d_residual); cudaFree(d_output);
}

TEST_F(BiasResidualTest, Large_128x4096) {
    const int rows = 128, cols = 4096;
    std::vector<float> h_input(rows * cols), h_bias(cols), h_residual(rows * cols);
    std::vector<float> h_ref(rows * cols);
    fill_random(h_input);
    fill_random(h_bias);
    fill_random(h_residual);

    cpu_bias_residual(h_ref.data(), h_input.data(), h_bias.data(),
                      h_residual.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_bias = to_device(h_bias);
    float* d_residual = to_device(h_residual);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_bias_residual(d_output, d_input, d_bias, d_residual, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-4f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_bias); cudaFree(d_residual); cudaFree(d_output);
}

TEST_F(BiasResidualTest, ZeroBias) {
    const int rows = 4, cols = 64;
    std::vector<float> h_input(rows * cols), h_bias(cols, 0.0f), h_residual(rows * cols);
    fill_random(h_input);
    fill_random(h_residual);

    float* d_input = to_device(h_input);
    float* d_bias = to_device(h_bias);
    float* d_residual = to_device(h_residual);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_bias_residual(d_output, d_input, d_bias, d_residual, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        float expected = h_input[i] + h_residual[i];
        EXPECT_NEAR(h_output[i], expected, 1e-5f)
            << "With zero bias, output should equal input + residual at index " << i;
    }

    cudaFree(d_input); cudaFree(d_bias); cudaFree(d_residual); cudaFree(d_output);
}

TEST_F(BiasResidualTest, NonMultipleOf256_Cols100) {
    const int rows = 8, cols = 100;
    std::vector<float> h_input(rows * cols), h_bias(cols), h_residual(rows * cols);
    std::vector<float> h_ref(rows * cols);
    fill_random(h_input);
    fill_random(h_bias);
    fill_random(h_residual);

    cpu_bias_residual(h_ref.data(), h_input.data(), h_bias.data(),
                      h_residual.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_bias = to_device(h_bias);
    float* d_residual = to_device(h_residual);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_bias_residual(d_output, d_input, d_bias, d_residual, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_bias); cudaFree(d_residual); cudaFree(d_output);
}
