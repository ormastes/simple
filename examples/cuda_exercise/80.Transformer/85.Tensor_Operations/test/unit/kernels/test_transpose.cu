/**
 * @file test_transpose.cu
 * @brief Unit tests for shared-memory-optimized matrix transpose kernel
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/transpose_permute.cuh"
#include <vector>
#include <cstdlib>
#include <cmath>

// ---------------------------------------------------------------------------
// CPU reference implementation
// ---------------------------------------------------------------------------

static void cpu_transpose(float* output, const float* input, int rows, int cols) {
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            output[c * rows + r] = input[r * cols + c];
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

class TransposeTest : public GpuTest {
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

TEST_F(TransposeTest, Square_32x32) {
    const int rows = 32, cols = 32;
    std::vector<float> h_input(rows * cols), h_ref(cols * rows);
    fill_random(h_input);

    cpu_transpose(h_ref.data(), h_input.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_transpose(d_output, d_input, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-6f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_output);
}

TEST_F(TransposeTest, Rectangular_64x128) {
    const int rows = 64, cols = 128;
    std::vector<float> h_input(rows * cols), h_ref(cols * rows);
    fill_random(h_input);

    cpu_transpose(h_ref.data(), h_input.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_transpose(d_output, d_input, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, cols * rows);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-6f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_output);
}

TEST_F(TransposeTest, Roundtrip_TransposeTwice) {
    const int rows = 48, cols = 96;
    std::vector<float> h_input(rows * cols);
    fill_random(h_input);

    float* d_input = to_device(h_input);
    float* d_temp = nullptr;
    float* d_output = nullptr;
    cudaMalloc(&d_temp, rows * cols * sizeof(float));
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    // First transpose: [rows, cols] -> [cols, rows]
    transformer::launch_transpose(d_temp, d_input, rows, cols);
    cudaDeviceSynchronize();

    // Second transpose: [cols, rows] -> [rows, cols]
    transformer::launch_transpose(d_output, d_temp, cols, rows);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, rows * cols);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_input[i], 1e-6f)
            << "Roundtrip mismatch at index " << i
            << " (transpose twice should yield identity)";
    }

    cudaFree(d_input); cudaFree(d_temp); cudaFree(d_output);
}

TEST_F(TransposeTest, NonTileAligned_37x73) {
    const int rows = 37, cols = 73;
    std::vector<float> h_input(rows * cols), h_ref(cols * rows);
    fill_random(h_input);

    cpu_transpose(h_ref.data(), h_input.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_transpose(d_output, d_input, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, cols * rows);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-6f)
            << "Mismatch at non-tile-aligned index " << i;
    }

    cudaFree(d_input); cudaFree(d_output);
}

TEST_F(TransposeTest, Large_256x512) {
    const int rows = 256, cols = 512;
    std::vector<float> h_input(rows * cols), h_ref(cols * rows);
    fill_random(h_input);

    cpu_transpose(h_ref.data(), h_input.data(), rows, cols);

    float* d_input = to_device(h_input);
    float* d_output = nullptr;
    cudaMalloc(&d_output, rows * cols * sizeof(float));

    transformer::launch_transpose(d_output, d_input, rows, cols);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, cols * rows);
    for (int i = 0; i < rows * cols; i++) {
        EXPECT_NEAR(h_output[i], h_ref[i], 1e-5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_output);
}
