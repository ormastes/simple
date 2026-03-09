/**
 * @file test_matmul_kernel.cu
 * @brief Unit tests for the tiled matmul CUDA kernel and helper kernels
 *
 * Tests the kernel launchers directly (bypassing the C API layer) to verify
 * numerical correctness, boundary handling, and auxiliary operations like
 * bias addition and softmax.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "matmul_kernel.h"
#include <cuda_runtime.h>
#include <vector>
#include <random>
#include <cmath>

/**
 * @brief Test fixture for kernel-level tests
 */
class MatmulKernelTest : public ::testing::Test {
protected:
    std::mt19937 gen{123};

    std::vector<float> randomVec(int n) {
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        std::vector<float> v(n);
        for (auto& x : v) x = dist(gen);
        return v;
    }

    std::vector<float> cpuMatmul(const std::vector<float>& A,
                                  const std::vector<float>& B,
                                  int M, int N, int K) {
        std::vector<float> C(M * N, 0.0f);
        for (int i = 0; i < M; ++i)
            for (int j = 0; j < N; ++j)
                for (int k = 0; k < K; ++k)
                    C[i * N + j] += A[i * K + k] * B[k * N + j];
        return C;
    }
};

TEST_F(MatmulKernelTest, ExactTileSize) {
    const int M = 32, K = 32, N = 32;
    auto hA = randomVec(M * K);
    auto hB = randomVec(K * N);
    auto ref = cpuMatmul(hA, hB, M, N, K);

    float *dA, *dB, *dC;
    cudaMalloc(&dA, sizeof(float) * M * K);
    cudaMalloc(&dB, sizeof(float) * K * N);
    cudaMalloc(&dC, sizeof(float) * M * N);
    cudaMemcpy(dA, hA.data(), sizeof(float) * M * K, cudaMemcpyHostToDevice);
    cudaMemcpy(dB, hB.data(), sizeof(float) * K * N, cudaMemcpyHostToDevice);

    launch_tiled_matmul(dC, dA, dB, M, N, K, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> hC(M * N);
    cudaMemcpy(hC.data(), dC, sizeof(float) * M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 1e-3f) << "At index " << i;
    }

    cudaFree(dA); cudaFree(dB); cudaFree(dC);
}

TEST_F(MatmulKernelTest, NonTileAligned) {
    const int M = 37, K = 19, N = 43;
    auto hA = randomVec(M * K);
    auto hB = randomVec(K * N);
    auto ref = cpuMatmul(hA, hB, M, N, K);

    float *dA, *dB, *dC;
    cudaMalloc(&dA, sizeof(float) * M * K);
    cudaMalloc(&dB, sizeof(float) * K * N);
    cudaMalloc(&dC, sizeof(float) * M * N);
    cudaMemcpy(dA, hA.data(), sizeof(float) * M * K, cudaMemcpyHostToDevice);
    cudaMemcpy(dB, hB.data(), sizeof(float) * K * N, cudaMemcpyHostToDevice);

    launch_tiled_matmul(dC, dA, dB, M, N, K, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> hC(M * N);
    cudaMemcpy(hC.data(), dC, sizeof(float) * M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 1e-2f) << "At index " << i;
    }

    cudaFree(dA); cudaFree(dB); cudaFree(dC);
}

TEST_F(MatmulKernelTest, SingleElement) {
    const int M = 1, K = 1, N = 1;
    float hA = 3.0f, hB = 4.0f;
    float *dA, *dB, *dC;
    cudaMalloc(&dA, sizeof(float));
    cudaMalloc(&dB, sizeof(float));
    cudaMalloc(&dC, sizeof(float));
    cudaMemcpy(dA, &hA, sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(dB, &hB, sizeof(float), cudaMemcpyHostToDevice);

    launch_tiled_matmul(dC, dA, dB, M, N, K, nullptr);
    cudaDeviceSynchronize();

    float hC;
    cudaMemcpy(&hC, dC, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_NEAR(hC, 12.0f, 1e-5f);

    cudaFree(dA); cudaFree(dB); cudaFree(dC);
}

TEST_F(MatmulKernelTest, LargeMatrix) {
    const int M = 128, K = 256, N = 128;
    auto hA = randomVec(M * K);
    auto hB = randomVec(K * N);
    auto ref = cpuMatmul(hA, hB, M, N, K);

    float *dA, *dB, *dC;
    cudaMalloc(&dA, sizeof(float) * M * K);
    cudaMalloc(&dB, sizeof(float) * K * N);
    cudaMalloc(&dC, sizeof(float) * M * N);
    cudaMemcpy(dA, hA.data(), sizeof(float) * M * K, cudaMemcpyHostToDevice);
    cudaMemcpy(dB, hB.data(), sizeof(float) * K * N, cudaMemcpyHostToDevice);

    launch_tiled_matmul(dC, dA, dB, M, N, K, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> hC(M * N);
    cudaMemcpy(hC.data(), dC, sizeof(float) * M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 5e-2f) << "At index " << i;
    }

    cudaFree(dA); cudaFree(dB); cudaFree(dC);
}

TEST_F(MatmulKernelTest, AddBias) {
    const int rows = 4, cols = 8;
    std::vector<float> hMat(rows * cols, 1.0f);
    std::vector<float> hBias(cols);
    for (int i = 0; i < cols; ++i) hBias[i] = static_cast<float>(i);

    float *dMat, *dBias;
    cudaMalloc(&dMat, sizeof(float) * rows * cols);
    cudaMalloc(&dBias, sizeof(float) * cols);
    cudaMemcpy(dMat, hMat.data(), sizeof(float) * rows * cols, cudaMemcpyHostToDevice);
    cudaMemcpy(dBias, hBias.data(), sizeof(float) * cols, cudaMemcpyHostToDevice);

    launch_add_bias(dMat, dBias, rows, cols, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> result(rows * cols);
    cudaMemcpy(result.data(), dMat, sizeof(float) * rows * cols, cudaMemcpyDeviceToHost);

    for (int i = 0; i < rows; ++i) {
        for (int j = 0; j < cols; ++j) {
            EXPECT_NEAR(result[i * cols + j], 1.0f + j, 1e-5f);
        }
    }

    cudaFree(dMat); cudaFree(dBias);
}

TEST_F(MatmulKernelTest, SoftmaxRowSums) {
    const int rows = 3, cols = 5;
    auto hInput = randomVec(rows * cols);

    float *dIn, *dOut;
    cudaMalloc(&dIn, sizeof(float) * rows * cols);
    cudaMalloc(&dOut, sizeof(float) * rows * cols);
    cudaMemcpy(dIn, hInput.data(), sizeof(float) * rows * cols, cudaMemcpyHostToDevice);

    launch_softmax(dOut, dIn, rows, cols, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> hOut(rows * cols);
    cudaMemcpy(hOut.data(), dOut, sizeof(float) * rows * cols, cudaMemcpyDeviceToHost);

    // Each row should sum to ~1.0 and all values should be non-negative
    for (int i = 0; i < rows; ++i) {
        float row_sum = 0.0f;
        for (int j = 0; j < cols; ++j) {
            EXPECT_GE(hOut[i * cols + j], 0.0f);
            row_sum += hOut[i * cols + j];
        }
        EXPECT_NEAR(row_sum, 1.0f, 1e-5f) << "Row " << i;
    }

    cudaFree(dIn); cudaFree(dOut);
}

TEST_F(MatmulKernelTest, ReduceRows) {
    const int rows = 4, cols = 3;
    std::vector<float> hInput(rows * cols);
    for (int i = 0; i < rows * cols; ++i) hInput[i] = static_cast<float>(i + 1);

    float *dIn, *dOut;
    cudaMalloc(&dIn, sizeof(float) * rows * cols);
    cudaMalloc(&dOut, sizeof(float) * cols);
    cudaMemcpy(dIn, hInput.data(), sizeof(float) * rows * cols, cudaMemcpyHostToDevice);

    launch_reduce_rows(dOut, dIn, rows, cols, nullptr);
    cudaDeviceSynchronize();

    std::vector<float> hOut(cols);
    cudaMemcpy(hOut.data(), dOut, sizeof(float) * cols, cudaMemcpyDeviceToHost);

    // Column sums: col0 = 1+4+7+10=22, col1 = 2+5+8+11=26, col2 = 3+6+9+12=30
    EXPECT_NEAR(hOut[0], 22.0f, 1e-5f);
    EXPECT_NEAR(hOut[1], 26.0f, 1e-5f);
    EXPECT_NEAR(hOut[2], 30.0f, 1e-5f);

    cudaFree(dIn); cudaFree(dOut);
}
