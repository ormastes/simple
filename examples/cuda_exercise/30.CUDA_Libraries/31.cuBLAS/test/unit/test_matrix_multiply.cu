#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cublas_v2.h>
#include <vector>
#include "cuda_utils.h"

class CublasMatmulTest : public GpuTest {
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

    // Helper: CPU reference implementation (row-major)
    void cpu_gemm(const float* A, const float* B, float* C,
                  int m, int n, int k) {
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                float sum = 0.0f;
                for (int p = 0; p < k; p++) {
                    sum += A[i * k + p] * B[p * n + j];
                }
                C[i * n + j] = sum;
            }
        }
    }
};

TEST_F(CublasMatmulTest, SmallMatrixMultiply) {
    const int M = 64, N = 64, K = 64;

    // Host matrices (row-major)
    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C_ref(M * N);
    std::vector<float> h_C_gpu(M * N);

    // Initialize with random values
    for (int i = 0; i < M * K; i++) h_A[i] = static_cast<float>(rand() % 100) / 100.0f;
    for (int i = 0; i < K * N; i++) h_B[i] = static_cast<float>(rand() % 100) / 100.0f;

    // CPU reference
    cpu_gemm(h_A.data(), h_B.data(), h_C_ref.data(), M, N, K);

    // GPU computation
    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    // For row-major C = A * B, use column-major C^T = B^T * A^T
    cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                N, M, K,
                &alpha,
                d_B, N,
                d_A, K,
                &beta,
                d_C, N);

    cudaMemcpy(h_C_gpu.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify results
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C_ref[i], h_C_gpu[i], 1e-3f);
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

TEST_F(CublasMatmulTest, IdentityMatrix) {
    const int N = 100;

    // Create identity matrix and test vector
    std::vector<float> h_I(N * N, 0.0f);
    std::vector<float> h_x(N * N);
    std::vector<float> h_result(N * N);

    // Initialize identity
    for (int i = 0; i < N; i++) {
        h_I[i * N + i] = 1.0f;
    }

    // Initialize test matrix with pattern
    for (int i = 0; i < N * N; i++) {
        h_x[i] = static_cast<float>(i);
    }

    // Allocate device memory
    float* d_I = cuda_malloc<float>(N * N);
    float* d_x = cuda_malloc<float>(N * N);
    float* d_result = cuda_malloc<float>(N * N);

    cudaMemcpy(d_I, h_I.data(), N * N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_x, h_x.data(), N * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    // I * x = x (using column-major transposition trick)
    cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                N, N, N,
                &alpha,
                d_x, N,
                d_I, N,
                &beta,
                d_result, N);

    cudaMemcpy(h_result.data(), d_result, N * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify I * x = x
    for (int i = 0; i < N * N; i++) {
        EXPECT_NEAR(h_result[i], h_x[i], 1e-5f);
    }

    cuda_free(d_I);
    cuda_free(d_x);
    cuda_free(d_result);
}

TEST_F(CublasMatmulTest, AlphaBetaScaling) {
    const int M = 50, N = 50, K = 50;

    // Simple matrices: A = ones, B = ones
    std::vector<float> h_A(M * K, 1.0f);
    std::vector<float> h_B(K * N, 1.0f);
    std::vector<float> h_C(M * N, 5.0f);  // Initial value

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_C, h_C.data(), M * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 2.0f, beta = 3.0f;

    // C = alpha * A * B + beta * C
    // C = 2 * (1*1*K) + 3 * 5 = 2*K + 15
    cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                N, M, K,
                &alpha,
                d_B, N,
                d_A, K,
                &beta,
                d_C, N);

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    float expected = alpha * K + beta * 5.0f;  // 2*50 + 3*5 = 100 + 15 = 115

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected, 1e-3f);
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

TEST_F(CublasMatmulTest, RectangularMatrices) {
    const int M = 100, N = 50, K = 75;

    std::vector<float> h_A(M * K, 1.0f);
    std::vector<float> h_B(K * N, 1.0f);
    std::vector<float> h_C(M * N);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                N, M, K,
                &alpha,
                d_B, N,
                d_A, K,
                &beta,
                d_C, N);

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Each element should be sum of K ones = K
    for (int i = 0; i < M * N; i++) {
        EXPECT_FLOAT_EQ(h_C[i], static_cast<float>(K));
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}
