#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cublas_v2.h>
#include <vector>
#include "cuda_utils.h"

class CublasBasicTest : public GpuTest {
protected:
    cublasHandle_t handle;

    void SetUp() override {
        GpuTest::SetUp();
        cublasStatus_t status = cublasCreate(&handle);
        ASSERT_EQ(status, CUBLAS_STATUS_SUCCESS);
    }

    void TearDown() override {
        cublasDestroy(handle);
        GpuTest::TearDown();
    }
};

TEST_F(CublasBasicTest, DotProduct) {
    const int n = 1024;
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(n);

    // Initialize with ones
    std::vector<float> ones(n, 1.0f);
    cudaMemcpy(d_x, ones.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_y, ones.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    float result;
    cublasSdot(handle, n, d_x, 1, d_y, 1, &result);
    cudaDeviceSynchronize();

    EXPECT_FLOAT_EQ(result, 1024.0f);

    cuda_free(d_x);
    cuda_free(d_y);
}

TEST_F(CublasBasicTest, VectorScaling) {
    const int n = 100;
    float* d_x = cuda_malloc<float>(n);

    // Initialize with 2.0
    std::vector<float> data(n, 2.0f);
    cudaMemcpy(d_x, data.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 3.0f;
    cublasSscal(handle, n, &alpha, d_x, 1);
    cudaDeviceSynchronize();

    // Read back
    cudaMemcpy(data.data(), d_x, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; i++) {
        EXPECT_FLOAT_EQ(data[i], 6.0f);
    }

    cuda_free(d_x);
}

TEST_F(CublasBasicTest, AXPY) {
    const int n = 100;
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(n);

    // x = ones, y = twos
    std::vector<float> x_data(n, 1.0f);
    std::vector<float> y_data(n, 2.0f);
    cudaMemcpy(d_x, x_data.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_y, y_data.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    // y = 3*x + y = 3*1 + 2 = 5
    float alpha = 3.0f;
    cublasSaxpy(handle, n, &alpha, d_x, 1, d_y, 1);
    cudaDeviceSynchronize();

    // Read back y
    cudaMemcpy(y_data.data(), d_y, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; i++) {
        EXPECT_FLOAT_EQ(y_data[i], 5.0f);
    }

    cuda_free(d_x);
    cuda_free(d_y);
}

TEST_F(CublasBasicTest, L2Norm) {
    const int n = 100;
    float* d_x = cuda_malloc<float>(n);

    // Initialize with 3.0
    std::vector<float> data(n, 3.0f);
    cudaMemcpy(d_x, data.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    float result;
    cublasSnrm2(handle, n, d_x, 1, &result);
    cudaDeviceSynchronize();

    // ||x||_2 = sqrt(100 * 3^2) = sqrt(900) = 30
    EXPECT_NEAR(result, 30.0f, 1e-5f);

    cuda_free(d_x);
}

TEST_F(CublasBasicTest, VectorCopy) {
    const int n = 100;
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(n);

    // Initialize x with pattern, y with zeros
    std::vector<float> x_data(n);
    std::vector<float> y_data(n, 0.0f);
    for (int i = 0; i < n; i++) {
        x_data[i] = static_cast<float>(i);
    }

    cudaMemcpy(d_x, x_data.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_y, y_data.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    // Copy x to y
    cublasScopy(handle, n, d_x, 1, d_y, 1);
    cudaDeviceSynchronize();

    // Read back y
    cudaMemcpy(y_data.data(), d_y, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; i++) {
        EXPECT_FLOAT_EQ(y_data[i], x_data[i]);
    }

    cuda_free(d_x);
    cuda_free(d_y);
}
