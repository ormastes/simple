/**
 * @file test_activation.cu
 * @brief Unit tests for MLP activation kernels (GELU, SiLU, SwiGLU, fp16 GELU)
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/activation.cuh"
#include <vector>
#include <cmath>
#include <cstdlib>

// ---------------------------------------------------------------------------
// CPU reference implementations
// ---------------------------------------------------------------------------

static float cpu_gelu(float x) {
    float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
    return x * cdf;
}

static float cpu_silu(float x) {
    return x / (1.0f + expf(-x));
}

static void fill_random(std::vector<float>& v, float lo = -3.0f, float hi = 3.0f) {
    for (auto& x : v) {
        x = lo + static_cast<float>(rand()) / RAND_MAX * (hi - lo);
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class ActivationTest : public GpuTest {
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
// GELU tests
// ---------------------------------------------------------------------------

TEST_F(ActivationTest, GELU_Correctness) {
    const int n = 1024;
    std::vector<float> h_input(n);
    fill_random(h_input);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, n * sizeof(float));

    transformer::launch_gelu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, n);
    for (int i = 0; i < n; i++) {
        float expected = cpu_gelu(h_input[i]);
        EXPECT_NEAR(h_output[i], expected, 1e-5f)
            << "GELU mismatch at index " << i << " (input=" << h_input[i] << ")";
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(ActivationTest, GELU_SpecialValues) {
    // GELU(0) = 0, GELU should be monotonically increasing for large positive x
    std::vector<float> h_input = {0.0f, 1.0f, -1.0f, 5.0f, -5.0f};
    int n = static_cast<int>(h_input.size());

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, n * sizeof(float));

    transformer::launch_gelu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, n);

    EXPECT_NEAR(h_output[0], 0.0f, 1e-6f);             // GELU(0) = 0
    EXPECT_GT(h_output[1], 0.0f);                        // GELU(1) > 0
    EXPECT_LT(h_output[2], 0.0f);                        // GELU(-1) < 0
    EXPECT_NEAR(h_output[3], 5.0f, 0.01f);              // GELU(5) ~ 5
    EXPECT_NEAR(h_output[4], 0.0f, 0.01f);              // GELU(-5) ~ 0

    cudaFree(d_input);
    cudaFree(d_output);
}

// ---------------------------------------------------------------------------
// SiLU tests
// ---------------------------------------------------------------------------

TEST_F(ActivationTest, SiLU_Correctness) {
    const int n = 1024;
    std::vector<float> h_input(n);
    fill_random(h_input);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, n * sizeof(float));

    transformer::launch_silu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, n);
    for (int i = 0; i < n; i++) {
        float expected = cpu_silu(h_input[i]);
        EXPECT_NEAR(h_output[i], expected, 1e-5f)
            << "SiLU mismatch at index " << i << " (input=" << h_input[i] << ")";
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(ActivationTest, SiLU_SpecialValues) {
    // SiLU(0) = 0, SiLU is smooth and monotonic for positive x
    std::vector<float> h_input = {0.0f, 1.0f, -1.0f, 10.0f};
    int n = static_cast<int>(h_input.size());

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, n * sizeof(float));

    transformer::launch_silu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, n);

    EXPECT_NEAR(h_output[0], 0.0f, 1e-6f);              // SiLU(0) = 0
    EXPECT_NEAR(h_output[1], cpu_silu(1.0f), 1e-5f);    // SiLU(1) ~ 0.7311
    EXPECT_LT(h_output[2], 0.0f);                        // SiLU(-1) < 0
    EXPECT_NEAR(h_output[3], 10.0f, 0.01f);             // SiLU(10) ~ 10

    cudaFree(d_input);
    cudaFree(d_output);
}

// ---------------------------------------------------------------------------
// SwiGLU tests
// ---------------------------------------------------------------------------

TEST_F(ActivationTest, SwiGLU_Correctness) {
    const int half_n = 512;
    const int n = half_n * 2;
    std::vector<float> h_input(n);
    fill_random(h_input);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, half_n * sizeof(float));

    transformer::launch_swiglu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, half_n);
    for (int i = 0; i < half_n; i++) {
        float x = h_input[i];
        float gate = h_input[i + half_n];
        float expected = gate * cpu_silu(x);
        EXPECT_NEAR(h_output[i], expected, 1e-4f)
            << "SwiGLU mismatch at index " << i;
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(ActivationTest, SwiGLU_ZeroGate) {
    // When gate is zero, output should be zero regardless of x
    const int half_n = 4;
    const int n = half_n * 2;
    std::vector<float> h_input = {1.0f, 2.0f, -1.0f, 3.0f,   // x values
                                   0.0f, 0.0f,  0.0f, 0.0f};  // gate = 0

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, half_n * sizeof(float));

    transformer::launch_swiglu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, half_n);
    for (int i = 0; i < half_n; i++) {
        EXPECT_NEAR(h_output[i], 0.0f, 1e-6f)
            << "SwiGLU with zero gate should be zero at index " << i;
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

// ---------------------------------------------------------------------------
// fp16 GELU tests
// ---------------------------------------------------------------------------

TEST_F(ActivationTest, GELU_FP16_Correctness) {
    const int n = 512;
    std::vector<float> h_input_fp32(n);
    fill_random(h_input_fp32, -2.0f, 2.0f);

    // Convert to fp16
    std::vector<half> h_input_fp16(n);
    for (int i = 0; i < n; i++) {
        h_input_fp16[i] = __float2half(h_input_fp32[i]);
    }

    half* d_input = nullptr;
    half* d_output = nullptr;
    cudaMalloc(&d_input, n * sizeof(half));
    cudaMalloc(&d_output, n * sizeof(half));
    cudaMemcpy(d_input, h_input_fp16.data(), n * sizeof(half), cudaMemcpyHostToDevice);

    transformer::launch_gelu_fp16(d_output, d_input, n);
    cudaDeviceSynchronize();

    std::vector<half> h_output_fp16(n);
    cudaMemcpy(h_output_fp16.data(), d_output, n * sizeof(half), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; i++) {
        float input_val = __half2float(h_input_fp16[i]);
        float expected = cpu_gelu(input_val);
        float actual = __half2float(h_output_fp16[i]);
        // fp16 has lower precision, use wider tolerance
        EXPECT_NEAR(actual, expected, 0.01f)
            << "fp16 GELU mismatch at index " << i << " (input=" << input_val << ")";
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

// ---------------------------------------------------------------------------
// Large tensor test
// ---------------------------------------------------------------------------

TEST_F(ActivationTest, GELU_LargeTensor) {
    const int n = 65536;  // Large enough to use multiple blocks
    std::vector<float> h_input(n);
    fill_random(h_input);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, n * sizeof(float));

    transformer::launch_gelu(d_output, d_input, n);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, n);

    // Spot-check a few elements
    for (int i = 0; i < n; i += 1000) {
        float expected = cpu_gelu(h_input[i]);
        EXPECT_NEAR(h_output[i], expected, 1e-5f)
            << "GELU large tensor mismatch at index " << i;
    }

    cudaFree(d_input);
    cudaFree(d_output);
}
