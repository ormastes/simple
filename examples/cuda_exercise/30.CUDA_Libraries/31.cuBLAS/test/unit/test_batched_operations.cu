#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cublas_v2.h>
#include <vector>
#include "cuda_utils.h"

class CublasBatchedTest : public GpuTest {
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

TEST_F(CublasBatchedTest, SmallBatchedGEMM) {
    const int M = 32, N = 32, K = 32;
    const int batch_count = 10;

    // Allocate batch of matrices
    std::vector<float*> h_A_ptrs(batch_count);
    std::vector<float*> h_B_ptrs(batch_count);
    std::vector<float*> h_C_ptrs(batch_count);

    for (int i = 0; i < batch_count; i++) {
        h_A_ptrs[i] = cuda_malloc<float>(M * K);
        h_B_ptrs[i] = cuda_malloc<float>(K * N);
        h_C_ptrs[i] = cuda_malloc<float>(M * N);

        // Initialize with simple pattern (all ones)
        std::vector<float> h_A(M * K, 1.0f);
        std::vector<float> h_B(K * N, 1.0f);
        cudaMemcpy(h_A_ptrs[i], h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
        cudaMemcpy(h_B_ptrs[i], h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);
    }

    // Copy pointer arrays to device
    float** d_A_ptrs = cuda_malloc<float*>(batch_count);
    float** d_B_ptrs = cuda_malloc<float*>(batch_count);
    float** d_C_ptrs = cuda_malloc<float*>(batch_count);

    cudaMemcpy(d_A_ptrs, h_A_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_ptrs, h_B_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_C_ptrs, h_C_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    // Batched GEMM
    cublasSgemmBatched(handle,
                       CUBLAS_OP_N, CUBLAS_OP_N,
                       M, N, K,
                       &alpha,
                       const_cast<const float**>(d_A_ptrs), M,
                       const_cast<const float**>(d_B_ptrs), K,
                       &beta,
                       d_C_ptrs, M,
                       batch_count);

    cudaDeviceSynchronize();

    // Verify results
    std::vector<float> h_C(M * N);
    for (int batch = 0; batch < batch_count; batch++) {
        cudaMemcpy(h_C.data(), h_C_ptrs[batch], M * N * sizeof(float), cudaMemcpyDeviceToHost);

        // Each element should be K (sum of K ones)
        for (int i = 0; i < M * N; i++) {
            EXPECT_FLOAT_EQ(h_C[i], static_cast<float>(K));
        }
    }

    // Cleanup
    for (int i = 0; i < batch_count; i++) {
        cuda_free(h_A_ptrs[i]);
        cuda_free(h_B_ptrs[i]);
        cuda_free(h_C_ptrs[i]);
    }

    cuda_free(d_A_ptrs);
    cuda_free(d_B_ptrs);
    cuda_free(d_C_ptrs);
}

TEST_F(CublasBatchedTest, StridedBatchedGEMM) {
    const int M = 16, N = 16, K = 16;
    const int batch_count = 5;

    const int matrix_size = M * K;

    // Allocate contiguous memory for all matrices
    float* d_A_all = cuda_malloc<float>(batch_count * M * K);
    float* d_B_all = cuda_malloc<float>(batch_count * K * N);
    float* d_C_all = cuda_malloc<float>(batch_count * M * N);

    // Initialize all matrices with ones
    std::vector<float> h_A_all(batch_count * M * K, 1.0f);
    std::vector<float> h_B_all(batch_count * K * N, 1.0f);

    cudaMemcpy(d_A_all, h_A_all.data(), batch_count * M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_all, h_B_all.data(), batch_count * K * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    // Strided batched GEMM
    cublasSgemmStridedBatched(handle,
                              CUBLAS_OP_N, CUBLAS_OP_N,
                              M, N, K,
                              &alpha,
                              d_A_all, M, M * K,  // stride_A
                              d_B_all, K, K * N,  // stride_B
                              &beta,
                              d_C_all, M, M * N,  // stride_C
                              batch_count);

    cudaDeviceSynchronize();

    // Verify results
    std::vector<float> h_C_all(batch_count * M * N);
    cudaMemcpy(h_C_all.data(), d_C_all, batch_count * M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < batch_count * M * N; i++) {
        EXPECT_FLOAT_EQ(h_C_all[i], static_cast<float>(K));
    }

    cuda_free(d_A_all);
    cuda_free(d_B_all);
    cuda_free(d_C_all);
}

TEST_F(CublasBatchedTest, DifferentInputsPerBatch) {
    const int M = 8, N = 8, K = 8;
    const int batch_count = 3;

    std::vector<float*> h_A_ptrs(batch_count);
    std::vector<float*> h_B_ptrs(batch_count);
    std::vector<float*> h_C_ptrs(batch_count);

    // Create different matrices for each batch
    std::vector<std::vector<float>> h_A_host(batch_count, std::vector<float>(M * K));
    std::vector<std::vector<float>> h_B_host(batch_count, std::vector<float>(K * N));

    for (int batch = 0; batch < batch_count; batch++) {
        h_A_ptrs[batch] = cuda_malloc<float>(M * K);
        h_B_ptrs[batch] = cuda_malloc<float>(K * N);
        h_C_ptrs[batch] = cuda_malloc<float>(M * N);

        // Different values for each batch
        for (int i = 0; i < M * K; i++) {
            h_A_host[batch][i] = static_cast<float>(batch + 1);
        }
        for (int i = 0; i < K * N; i++) {
            h_B_host[batch][i] = 1.0f;
        }

        cudaMemcpy(h_A_ptrs[batch], h_A_host[batch].data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
        cudaMemcpy(h_B_ptrs[batch], h_B_host[batch].data(), K * N * sizeof(float), cudaMemcpyHostToDevice);
    }

    float** d_A_ptrs = cuda_malloc<float*>(batch_count);
    float** d_B_ptrs = cuda_malloc<float*>(batch_count);
    float** d_C_ptrs = cuda_malloc<float*>(batch_count);

    cudaMemcpy(d_A_ptrs, h_A_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_ptrs, h_B_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_C_ptrs, h_C_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    cublasSgemmBatched(handle,
                       CUBLAS_OP_N, CUBLAS_OP_N,
                       M, N, K,
                       &alpha,
                       const_cast<const float**>(d_A_ptrs), M,
                       const_cast<const float**>(d_B_ptrs), K,
                       &beta,
                       d_C_ptrs, M,
                       batch_count);

    cudaDeviceSynchronize();

    // Verify: each batch should have different results
    std::vector<float> h_C(M * N);
    for (int batch = 0; batch < batch_count; batch++) {
        cudaMemcpy(h_C.data(), h_C_ptrs[batch], M * N * sizeof(float), cudaMemcpyDeviceToHost);

        // Expected: (batch+1) * K
        float expected = static_cast<float>((batch + 1) * K);
        for (int i = 0; i < M * N; i++) {
            EXPECT_FLOAT_EQ(h_C[i], expected);
        }
    }

    // Cleanup
    for (int i = 0; i < batch_count; i++) {
        cuda_free(h_A_ptrs[i]);
        cuda_free(h_B_ptrs[i]);
        cuda_free(h_C_ptrs[i]);
    }

    cuda_free(d_A_ptrs);
    cuda_free(d_B_ptrs);
    cuda_free(d_C_ptrs);
}
