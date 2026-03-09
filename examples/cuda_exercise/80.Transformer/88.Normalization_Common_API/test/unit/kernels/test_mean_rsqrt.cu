/**
 * @file test_mean_rsqrt.cu
 * @brief Unit tests for mean, variance, and RMS reciprocal square root helpers
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/mean_rsqrt.cuh"
#include <vector>
#include <numeric>
#include <cmath>

// ---------------------------------------------------------------------------
// Test kernels
// ---------------------------------------------------------------------------

/**
 * @brief Kernel that computes the mean of an input array
 */
__global__ void kernel_compute_mean(const float* input, int n, float* result) {
    extern __shared__ float smem[];
    float mean = transformer::compute_mean(input, n, smem);
    if (threadIdx.x == 0) {
        result[0] = mean;
    }
}

/**
 * @brief Kernel that computes the variance of an input array given its mean
 */
__global__ void kernel_compute_variance(const float* input, float mean, int n, float* result) {
    extern __shared__ float smem[];
    float var = transformer::compute_variance(input, mean, n, smem);
    if (threadIdx.x == 0) {
        result[0] = var;
    }
}

/**
 * @brief Kernel that computes the RMS reciprocal square root
 */
__global__ void kernel_compute_rms_rsqrt(const float* input, int n, float eps, float* result) {
    extern __shared__ float smem[];
    float rms_inv = transformer::compute_rms_rsqrt(input, n, eps, smem);
    if (threadIdx.x == 0) {
        result[0] = rms_inv;
    }
}

/**
 * @brief Kernel that computes mean and variance together (typical LayerNorm pattern)
 */
__global__ void kernel_mean_and_variance(const float* input, int n, float* out_mean, float* out_var) {
    extern __shared__ float smem[];
    float mean = transformer::compute_mean(input, n, smem);
    if (threadIdx.x == 0) {
        out_mean[0] = mean;
    }
    __syncthreads();
    float var = transformer::compute_variance(input, mean, n, smem);
    if (threadIdx.x == 0) {
        out_var[0] = var;
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class MeanRsqrtTest : public GpuTest {
protected:
    float* d_input = nullptr;
    float* d_result = nullptr;
    float* d_result2 = nullptr;
    int blockSize = 256;

    void SetUp() override {
        GpuTest::SetUp();
        cudaMalloc(&d_result, sizeof(float));
        cudaMalloc(&d_result2, sizeof(float));
        cudaMemset(d_result, 0, sizeof(float));
        cudaMemset(d_result2, 0, sizeof(float));
    }

    void TearDown() override {
        if (d_input) cudaFree(d_input);
        if (d_result) cudaFree(d_result);
        if (d_result2) cudaFree(d_result2);
        GpuTest::TearDown();
    }

    void allocAndCopy(const std::vector<float>& data) {
        if (d_input) cudaFree(d_input);
        cudaMalloc(&d_input, data.size() * sizeof(float));
        cudaMemcpy(d_input, data.data(), data.size() * sizeof(float), cudaMemcpyHostToDevice);
    }

    float getResult() {
        float h;
        cudaMemcpy(&h, d_result, sizeof(float), cudaMemcpyDeviceToHost);
        return h;
    }

    float getResult2() {
        float h;
        cudaMemcpy(&h, d_result2, sizeof(float), cudaMemcpyDeviceToHost);
        return h;
    }

    size_t smemSize() {
        return ((blockSize + 31) / 32) * sizeof(float);
    }

    /// @brief CPU reference: compute mean
    float cpuMean(const std::vector<float>& data) {
        double sum = 0.0;
        for (float v : data) sum += v;
        return static_cast<float>(sum / data.size());
    }

    /// @brief CPU reference: compute variance given mean
    float cpuVariance(const std::vector<float>& data, float mean) {
        double sum = 0.0;
        for (float v : data) {
            double d = v - mean;
            sum += d * d;
        }
        return static_cast<float>(sum / data.size());
    }

    /// @brief CPU reference: compute rms rsqrt
    float cpuRmsRsqrt(const std::vector<float>& data, float eps) {
        double sum_sq = 0.0;
        for (float v : data) sum_sq += static_cast<double>(v) * v;
        double rms = sum_sq / data.size();
        return static_cast<float>(1.0 / std::sqrt(rms + eps));
    }
};

// ---------------------------------------------------------------------------
// Mean tests
// ---------------------------------------------------------------------------

TEST_F(MeanRsqrtTest, MeanAllOnes) {
    // All 1.0 -> mean = 1.0
    int n = 512;
    std::vector<float> data(n, 1.0f);
    allocAndCopy(data);

    kernel_compute_mean<<<1, blockSize, smemSize()>>>(d_input, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), 1.0f, 1e-5f);
}

TEST_F(MeanRsqrtTest, MeanArithmeticSequence) {
    // [1, 2, 3, ..., 256] -> mean = (1+256)/2 = 128.5
    int n = 256;
    std::vector<float> data(n);
    for (int i = 0; i < n; i++) data[i] = static_cast<float>(i + 1);
    allocAndCopy(data);

    kernel_compute_mean<<<1, blockSize, smemSize()>>>(d_input, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), 128.5f, 1e-3f);
}

TEST_F(MeanRsqrtTest, MeanLargeArray) {
    // 1024 elements with known mean
    int n = 1024;
    std::vector<float> data(n);
    for (int i = 0; i < n; i++) data[i] = static_cast<float>(i) * 0.01f;
    allocAndCopy(data);

    float expected = cpuMean(data);

    kernel_compute_mean<<<1, blockSize, smemSize()>>>(d_input, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected, 1e-3f);
}

TEST_F(MeanRsqrtTest, MeanAllZeros) {
    // All 0.0 -> mean = 0.0
    int n = 128;
    std::vector<float> data(n, 0.0f);
    allocAndCopy(data);

    kernel_compute_mean<<<1, blockSize, smemSize()>>>(d_input, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), 0.0f, 1e-6f);
}

// ---------------------------------------------------------------------------
// Variance tests
// ---------------------------------------------------------------------------

TEST_F(MeanRsqrtTest, VarianceAllOnes) {
    // All 1.0 -> mean = 1.0, variance = 0.0
    int n = 512;
    std::vector<float> data(n, 1.0f);
    allocAndCopy(data);

    kernel_compute_variance<<<1, blockSize, smemSize()>>>(d_input, 1.0f, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), 0.0f, 1e-5f);
}

TEST_F(MeanRsqrtTest, VarianceArithmeticSequence) {
    // [1, 2, 3, ..., 256]
    int n = 256;
    std::vector<float> data(n);
    for (int i = 0; i < n; i++) data[i] = static_cast<float>(i + 1);
    allocAndCopy(data);

    float mean = cpuMean(data);
    float expected_var = cpuVariance(data, mean);

    kernel_compute_variance<<<1, blockSize, smemSize()>>>(d_input, mean, n, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected_var, 1.0f);
}

TEST_F(MeanRsqrtTest, MeanAndVarianceTogether) {
    // Test the typical LayerNorm pattern: compute mean, then variance
    int n = 512;
    std::vector<float> data(n);
    for (int i = 0; i < n; i++) data[i] = static_cast<float>(i) * 0.1f - 25.0f;
    allocAndCopy(data);

    float expected_mean = cpuMean(data);
    float expected_var = cpuVariance(data, expected_mean);

    kernel_mean_and_variance<<<1, blockSize, smemSize()>>>(d_input, n, d_result, d_result2);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected_mean, 1e-2f);
    EXPECT_NEAR(getResult2(), expected_var, 1.0f);
}

// ---------------------------------------------------------------------------
// RMS rsqrt tests
// ---------------------------------------------------------------------------

TEST_F(MeanRsqrtTest, RmsRsqrtAllOnes) {
    // All 1.0 -> mean(x^2) = 1.0 -> rsqrt(1.0 + eps) ~ 1.0
    int n = 256;
    float eps = 1e-5f;
    std::vector<float> data(n, 1.0f);
    allocAndCopy(data);

    float expected = cpuRmsRsqrt(data, eps);

    kernel_compute_rms_rsqrt<<<1, blockSize, smemSize()>>>(d_input, n, eps, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected, 1e-5f);
}

TEST_F(MeanRsqrtTest, RmsRsqrtAllTwos) {
    // All 2.0 -> mean(x^2) = 4.0 -> rsqrt(4.0 + eps) ~ 0.5
    int n = 256;
    float eps = 1e-5f;
    std::vector<float> data(n, 2.0f);
    allocAndCopy(data);

    float expected = cpuRmsRsqrt(data, eps);

    kernel_compute_rms_rsqrt<<<1, blockSize, smemSize()>>>(d_input, n, eps, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected, 1e-5f);
}

TEST_F(MeanRsqrtTest, RmsRsqrtArithmeticSequence) {
    // [1, 2, ..., 512]
    int n = 512;
    float eps = 1e-6f;
    std::vector<float> data(n);
    for (int i = 0; i < n; i++) data[i] = static_cast<float>(i + 1);
    allocAndCopy(data);

    float expected = cpuRmsRsqrt(data, eps);

    kernel_compute_rms_rsqrt<<<1, blockSize, smemSize()>>>(d_input, n, eps, d_result);
    cudaDeviceSynchronize();

    EXPECT_NEAR(getResult(), expected, 1e-5f);
}

TEST_F(MeanRsqrtTest, RmsRsqrtSmallValues) {
    // Small values near zero - eps should prevent division by zero
    int n = 128;
    float eps = 1e-5f;
    std::vector<float> data(n, 1e-10f);
    allocAndCopy(data);

    float expected = cpuRmsRsqrt(data, eps);

    kernel_compute_rms_rsqrt<<<1, blockSize, smemSize()>>>(d_input, n, eps, d_result);
    cudaDeviceSynchronize();

    float result = getResult();
    EXPECT_TRUE(std::isfinite(result)) << "Result should be finite for small values with eps";
    EXPECT_NEAR(result, expected, 1.0f);
}
