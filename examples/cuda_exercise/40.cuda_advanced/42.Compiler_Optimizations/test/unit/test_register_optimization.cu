// test_register_optimization.cu - Tests for register optimization kernels

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/register_optimization.cu"
#include <cmath>

class RegisterOptimizationTest : public GpuTest {};

TEST_F(RegisterOptimizationTest, HighRegisterKernelProducesCorrectResults) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100) / 100.0f;
    }

    // Allocate device memory
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernel
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    high_register_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify results
    for (int i = 0; i < N; i++) {
        float a1 = h_input[i];
        float a2 = a1 * 2.0f;
        float a3 = a2 + 1.0f;
        float a4 = sinf(a3);
        float a5 = cosf(a3);
        float a6 = a4 * a5;
        float a7 = a6 + a1;
        float expected = sqrtf(fabsf(a7));

        EXPECT_NEAR(h_output[i], expected, 1e-5f) << "Mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(RegisterOptimizationTest, LowRegisterKernelProducesCorrectResults) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100) / 100.0f;
    }

    // Allocate device memory
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernel with launch bounds
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    low_register_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify results
    for (int i = 0; i < N; i++) {
        float val = h_input[i];
        float orig = val;
        val = val * 2.0f + 1.0f;
        float temp = sinf(val);
        val = temp * cosf(val) + orig;
        float expected = sqrtf(fabsf(val));

        EXPECT_NEAR(h_output[i], expected, 1e-5f) << "Mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(RegisterOptimizationTest, HighAndLowRegisterKernelsProduceSameResults) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output_high = new float[N];
    float* h_output_low = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100) / 100.0f;
    }

    // Allocate device memory
    float* d_input = cuda_malloc<float>(N);
    float* d_output_high = cuda_malloc<float>(N);
    float* d_output_low = cuda_malloc<float>(N);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernels
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    high_register_kernel<<<blocks, threads>>>(d_output_high, d_input, N);
    low_register_kernel<<<blocks, threads>>>(d_output_low, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy results back
    cuda_memcpy_d2h(h_output_high, d_output_high, N);
    cuda_memcpy_d2h(h_output_low, d_output_low, N);

    // Verify both produce same results
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_output_high[i], h_output_low[i], 1e-5f)
            << "Results differ at index " << i;
    }

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output_high);
    cuda_free(d_output_low);
    delete[] h_input;
    delete[] h_output_high;
    delete[] h_output_low;
}

TEST_F(RegisterOptimizationTest, OccupancyOptimizedKernelWorks) {
    const int N = 1024;
    float* h_data = new float[N];

    // Initialize data
    for (int i = 0; i < N; i++) {
        h_data[i] = static_cast<float>(i);
    }

    // Allocate device memory
    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    // Launch kernel
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    occupancy_optimized_kernel<<<blocks, threads>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify results
    for (int i = 0; i < N; i++) {
        float expected = static_cast<float>(i) * 2.0f + 1.0f;
        EXPECT_FLOAT_EQ(h_data[i], expected) << "Mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(RegisterOptimizationTest, PerformanceFirstKernelWorks) {
    const int N = 1024;
    float* h_data = new float[N];

    // Initialize data
    for (int i = 0; i < N; i++) {
        h_data[i] = 2.0f;
    }

    // Allocate device memory
    float* d_data = cuda_malloc<float>(N);
    cuda_memcpy_h2d(d_data, h_data, N);

    // Launch kernel
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    performance_first_kernel<<<blocks, threads>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify results (2^4 = 16)
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_data[i], 16.0f) << "Mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_data);
    delete[] h_data;
}
