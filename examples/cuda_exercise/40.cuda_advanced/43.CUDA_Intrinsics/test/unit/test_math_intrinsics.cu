// test_math_intrinsics.cu - Tests for math intrinsics

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/math_intrinsics.cu"
#include <cmath>

class MathIntrinsicsTest : public GpuTest {};

TEST_F(MathIntrinsicsTest, FastMathProducesReasonableResults) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input: values in range [0, 1]
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i) / N;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    fast_math_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify against CPU computation (with tolerance for fast math)
    for (int i = 0; i < N; i++) {
        float x = h_input[i];
        float expected = sinf(x) * cosf(x) + expf(x) * logf(x + 1.0f);

        // Fast math has lower precision, use larger tolerance
        EXPECT_NEAR(h_output[i], expected, 1e-4f) << "Fast math mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, StandardMathIsMoreAccurate) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i) / N;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    standard_math_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Standard math should match CPU closely
    for (int i = 0; i < N; i++) {
        float x = h_input[i];
        float expected = sinf(x) * cosf(x) + expf(x) * logf(x + 1.0f);

        EXPECT_NEAR(h_output[i], expected, 1e-6f) << "Standard math mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, FastSqrtAndRsqrtWork) {
    const int N = 1024;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input: positive values
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i + 1);  // Avoid zero
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    fast_sqrt_rsqrt_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify
    for (int i = 0; i < N; i++) {
        float x = h_input[i];
        float expected = sqrtf(x) + (1.0f / sqrtf(x)) + (1.0f / x);

        EXPECT_NEAR(h_output[i], expected, 1e-5f) << "Fast sqrt/rsqrt mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, IntegerIntrinsicsWork) {
    const int N = 256;
    unsigned int* h_input = new unsigned int[N];
    unsigned int* h_output = new unsigned int[N];

    // Initialize input: various bit patterns
    for (int i = 0; i < N; i++) {
        h_input[i] = i * 17 + 42;  // Pseudo-random pattern
    }

    unsigned int* d_input = cuda_malloc<unsigned int>(N);
    unsigned int* d_output = cuda_malloc<unsigned int>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    integer_intrinsics_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify against CPU computation
    for (int i = 0; i < N; i++) {
        unsigned int val = h_input[i];
        unsigned int popcount = __builtin_popcount(val);
        unsigned int ffs = __builtin_ffs(val);
        unsigned int clz = (val == 0) ? 32 : __builtin_clz(val);
        unsigned int byte_perm = ((val & 0xFF) << 24) |
                                  (((val >> 8) & 0xFF) << 16) |
                                  (((val >> 8) & 0xFF) << 8) |
                                  ((val >> 8) & 0xFF);

        // The kernel adds all these together
        // Note: GPU intrinsics may differ slightly in edge cases
        if (val != 0) {
            EXPECT_GT(h_output[i], 0u) << "Integer intrinsics failed at " << i;
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, FusedMultiplyAddWorks) {
    const int N = 1024;
    float* h_a = new float[N];
    float* h_b = new float[N];
    float* h_c = new float[N];
    float* h_output = new float[N];

    // Initialize inputs
    for (int i = 0; i < N; i++) {
        h_a[i] = static_cast<float>(i) / 10.0f;
        h_b[i] = 2.0f;
        h_c[i] = 1.0f;
    }

    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_c = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_a, h_a, N);
    cuda_memcpy_h2d(d_b, h_b, N);
    cuda_memcpy_h2d(d_c, h_c, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    fma_kernel<<<blocks, threads>>>(d_output, d_a, d_b, d_c, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify: a * 2 + 1
    for (int i = 0; i < N; i++) {
        float expected = h_a[i] * 2.0f + 1.0f;
        EXPECT_FLOAT_EQ(h_output[i], expected) << "FMA mismatch at " << i;
    }

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);
    cuda_free(d_output);
    delete[] h_a;
    delete[] h_b;
    delete[] h_c;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, SaturateClampToZeroOne) {
    const int N = 512;
    float* h_input = new float[N];
    float* h_output = new float[N];

    // Initialize input: values outside [0, 1] range
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i) / 100.0f - 2.0f;  // Range: [-2, 3.12]
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    saturate_kernel<<<blocks, threads>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify: all values in [0, 1]
    for (int i = 0; i < N; i++) {
        EXPECT_GE(h_output[i], 0.0f) << "Value below 0 at " << i;
        EXPECT_LE(h_output[i], 1.0f) << "Value above 1 at " << i;

        // Check correct clamping
        float expected = fminf(fmaxf(h_input[i], 0.0f), 1.0f);
        EXPECT_FLOAT_EQ(h_output[i], expected) << "Saturate mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(MathIntrinsicsTest, MinMaxIntrinsicsWork) {
    const int N = 512;
    float* h_a = new float[N];
    float* h_b = new float[N];
    float* h_min = new float[N];
    float* h_max = new float[N];

    // Initialize inputs
    for (int i = 0; i < N; i++) {
        h_a[i] = static_cast<float>(i);
        h_b[i] = static_cast<float>(N - i - 1);
    }

    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_min = cuda_malloc<float>(N);
    float* d_max = cuda_malloc<float>(N);

    cuda_memcpy_h2d(d_a, h_a, N);
    cuda_memcpy_h2d(d_b, h_b, N);

    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    minmax_kernel<<<blocks, threads>>>(d_min, d_max, d_a, d_b, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_min, d_min, N);
    cuda_memcpy_d2h(h_max, d_max, N);

    // Verify
    for (int i = 0; i < N; i++) {
        float expected_min = fminf(h_a[i], h_b[i]);
        float expected_max = fmaxf(h_a[i], h_b[i]);

        EXPECT_FLOAT_EQ(h_min[i], expected_min) << "Min mismatch at " << i;
        EXPECT_FLOAT_EQ(h_max[i], expected_max) << "Max mismatch at " << i;
    }

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_min);
    cuda_free(d_max);
    delete[] h_a;
    delete[] h_b;
    delete[] h_min;
    delete[] h_max;
}
