/**
 * @file test_rmsnorm.cu
 * @brief Unit tests for RMSNorm kernel correctness
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/rmsnorm.cuh"
#include <vector>
#include <cmath>
#include <cstdlib>
#include <numeric>

// ---------------------------------------------------------------------------
// CPU reference implementation
// ---------------------------------------------------------------------------

static void cpu_rmsnorm(float* output, const float* input, const float* weight,
                        int batch_size, int hidden_dim, float eps) {
    for (int b = 0; b < batch_size; b++) {
        const float* row = input + b * hidden_dim;
        float* out_row = output + b * hidden_dim;

        // Compute sum of squares
        float sum_sq = 0.0f;
        for (int i = 0; i < hidden_dim; i++) {
            sum_sq += row[i] * row[i];
        }
        float rms_scale = 1.0f / sqrtf(sum_sq / static_cast<float>(hidden_dim) + eps);

        // Normalize and scale
        for (int i = 0; i < hidden_dim; i++) {
            out_row[i] = weight[i] * row[i] * rms_scale;
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

class RMSNormTest : public GpuTest {
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

TEST_F(RMSNormTest, Small_HiddenDim64) {
    const int batch = 4, hidden = 64;
    std::vector<float> h_input(batch * hidden), h_weight(hidden), h_ref(batch * hidden);
    fill_random(h_input);
    fill_random(h_weight, 0.5f, 1.5f);

    cpu_rmsnorm(h_ref.data(), h_input.data(), h_weight.data(), batch, hidden, 1e-6f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);
    for (int i = 0; i < batch * hidden; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-4f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}

TEST_F(RMSNormTest, Medium_HiddenDim256) {
    const int batch = 8, hidden = 256;
    std::vector<float> h_input(batch * hidden), h_weight(hidden), h_ref(batch * hidden);
    fill_random(h_input);
    fill_random(h_weight, 0.5f, 1.5f);

    cpu_rmsnorm(h_ref.data(), h_input.data(), h_weight.data(), batch, hidden, 1e-6f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);
    for (int i = 0; i < batch * hidden; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-4f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}

TEST_F(RMSNormTest, Large_HiddenDim4096) {
    const int batch = 2, hidden = 4096;
    std::vector<float> h_input(batch * hidden), h_weight(hidden), h_ref(batch * hidden);
    fill_random(h_input);
    fill_random(h_weight, 0.8f, 1.2f);

    cpu_rmsnorm(h_ref.data(), h_input.data(), h_weight.data(), batch, hidden, 1e-6f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);
    for (int i = 0; i < batch * hidden; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-3f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}

TEST_F(RMSNormTest, UnityWeight) {
    // With weight = 1.0, RMSNorm just normalizes by the RMS
    const int batch = 2, hidden = 128;
    std::vector<float> h_input(batch * hidden), h_weight(hidden, 1.0f), h_ref(batch * hidden);
    fill_random(h_input);

    cpu_rmsnorm(h_ref.data(), h_input.data(), h_weight.data(), batch, hidden, 1e-6f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);

    // Verify that each row has unit RMS after normalization
    for (int b = 0; b < batch; b++) {
        float sum_sq = 0.0f;
        for (int i = 0; i < hidden; i++) {
            float v = h_output[b * hidden + i];
            sum_sq += v * v;
        }
        float rms = sqrtf(sum_sq / hidden);
        EXPECT_NEAR(rms, 1.0f, 1e-3f)
            << "Row " << b << " RMS should be ~1.0";
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}

TEST_F(RMSNormTest, ConstantInput) {
    // If all inputs in a row are the same value c, RMS = |c|,
    // so normalized output[i] = weight[i] * c / |c| = weight[i] * sign(c)
    const int batch = 1, hidden = 64;
    const float c = 3.0f;
    std::vector<float> h_input(batch * hidden, c);
    std::vector<float> h_weight(hidden);
    fill_random(h_weight, 0.5f, 1.5f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);

    // Expected: weight[i] * c * rsqrt(c^2 + eps) ~ weight[i] * sign(c) for eps << c^2
    float rms_scale = 1.0f / sqrtf(c * c + 1e-6f);
    for (int i = 0; i < hidden; i++) {
        float expected = h_weight[i] * c * rms_scale;
        EXPECT_NEAR(h_output[i], expected, 1e-4f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}

TEST_F(RMSNormTest, NonMultipleOf32_HiddenDim100) {
    // Test with hidden dim not aligned to warp size
    const int batch = 4, hidden = 100;
    std::vector<float> h_input(batch * hidden), h_weight(hidden), h_ref(batch * hidden);
    fill_random(h_input);
    fill_random(h_weight, 0.5f, 1.5f);

    cpu_rmsnorm(h_ref.data(), h_input.data(), h_weight.data(), batch, hidden, 1e-6f);

    float* d_input = to_device(h_input);
    float* d_weight = to_device(h_weight);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * hidden * sizeof(float));

    transformer::launch_rmsnorm(d_output, d_input, d_weight, batch, hidden);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * hidden);
    for (int i = 0; i < batch * hidden; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-4f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weight); cudaFree(d_output);
}
