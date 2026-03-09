/**
 * Multi-GPU Matrix Multiplication Tests (Module 27)
 *
 * Tests multi-GPU matrix multiplication kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "multi_gpu_manager.h"
#include <vector>
#include <cmath>

// Kernel declarations
template<int TILE_SIZE>
__global__ void matmul_tiled_multi_gpu(
    const float*, const float*, float*,
    int, int, int, int, int);

template<int TILE_SIZE>
__global__ void matmul_tiled_p2p(
    const float*, const float*, float*,
    int, int, int);

class MultiGPUMatMulTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        // Check if we have multiple GPUs
        int deviceCount;
        cudaGetDeviceCount(&deviceCount);

        if (deviceCount < 2) {
            GTEST_SKIP() << "Multi-GPU tests require at least 2 GPUs";
        }

        mgr = new MultiGPUManager();
        mgr->setupPeerAccess();
        mgr->printTopology();
    }

    void TearDown() override {
        delete mgr;
        GpuTest::TearDown();
    }

    MultiGPUManager* mgr;
};

TEST_F(MultiGPUMatMulTest, SmallMatrixDistributed) {
    const int M = 64, N = 64, K = 64;
    const int TILE_SIZE = 16;

    int deviceCount = mgr->getDeviceCount();

    // Prepare host matrices
    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C(M * N, 0.0f);
    std::vector<float> h_C_ref(M * N, 0.0f);

    // Initialize with simple values
    for (int i = 0; i < M * K; i++) h_A[i] = static_cast<float>(i % 10);
    for (int i = 0; i < K * N; i++) h_B[i] = static_cast<float>(i % 10);

    // Compute reference on CPU
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += h_A[i * K + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    // Distribute rows across GPUs
    auto distribution = mgr->distributeWork(M);

    std::vector<float*> d_A(deviceCount);
    std::vector<float*> d_B(deviceCount);
    std::vector<float*> d_C(deviceCount);

    int rowOffset = 0;
    for (int dev = 0; dev < deviceCount; dev++) {
        int M_local = distribution[dev];
        if (M_local == 0) continue;

        cudaSetDevice(dev);

        // Allocate device memory
        cudaMalloc(&d_A[dev], M_local * K * sizeof(float));
        cudaMalloc(&d_B[dev], K * N * sizeof(float));
        cudaMalloc(&d_C[dev], M_local * N * sizeof(float));

        // Copy data
        cudaMemcpy(d_A[dev], &h_A[rowOffset * K],
                   M_local * K * sizeof(float),
                   cudaMemcpyHostToDevice);
        cudaMemcpy(d_B[dev], h_B.data(),
                   K * N * sizeof(float),
                   cudaMemcpyHostToDevice);

        // Launch kernel
        dim3 block(TILE_SIZE, TILE_SIZE);
        dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE,
                  (M_local + TILE_SIZE - 1) / TILE_SIZE);

        matmul_tiled_multi_gpu<TILE_SIZE><<<grid, block>>>(
            d_A[dev], d_B[dev], d_C[dev],
            M, N, K, rowOffset, M_local);

        CHECK_KERNEL_LAUNCH();

        rowOffset += M_local;
    }

    // Gather results
    rowOffset = 0;
    for (int dev = 0; dev < deviceCount; dev++) {
        int M_local = distribution[dev];
        if (M_local == 0) continue;

        cudaSetDevice(dev);
        cudaMemcpy(&h_C[rowOffset * N], d_C[dev],
                   M_local * N * sizeof(float),
                   cudaMemcpyDeviceToHost);

        rowOffset += M_local;
    }

    // Verify results
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f)
            << "Mismatch at index " << i;
    }

    // Cleanup
    for (int dev = 0; dev < deviceCount; dev++) {
        if (distribution[dev] == 0) continue;

        cudaSetDevice(dev);
        cudaFree(d_A[dev]);
        cudaFree(d_B[dev]);
        cudaFree(d_C[dev]);
    }
}

TEST_F(MultiGPUMatMulTest, LoadBalancing) {
    // Test that work is distributed based on GPU capabilities
    const int M = 1000;

    auto distribution = mgr->distributeWork(M);

    int totalAssigned = 0;
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        EXPECT_GT(distribution[dev], 0) << "GPU " << dev << " got no work";
        totalAssigned += distribution[dev];
        printf("GPU %d: %d rows (%.1f%%)\n",
               dev, distribution[dev],
               100.0f * distribution[dev] / M);
    }

    EXPECT_EQ(totalAssigned, M) << "Work distribution doesn't sum to total";
}

TEST_F(MultiGPUMatMulTest, PeerAccessCheck) {
    // Verify peer access is set up correctly
    int deviceCount = mgr->getDeviceCount();

    for (int i = 0; i < deviceCount; i++) {
        for (int j = 0; j < deviceCount; j++) {
            if (i != j) {
                bool canAccess = mgr->canAccessPeer(i, j);
                printf("GPU %d -> GPU %d: %s\n",
                       i, j, canAccess ? "YES" : "NO");
            }
        }
    }

    SUCCEED();
}
