/**
 * Unit tests for dynamic matrix multiplication kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"

// Include kernel implementations
#include "../../../src/kernels/matrix_multiply_dynamic.cu"

// Test fixture
class MatMulDynamicTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        // Check if dynamic parallelism is supported
        cudaDeviceProp prop;
        CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

        if (prop.major < 3 || (prop.major == 3 && prop.minor < 5)) {
            GTEST_SKIP() << "Dynamic Parallelism not supported (requires CC 3.5+)";
        }
    }
};

// ============================================================================
// Helper Functions
// ============================================================================

// CPU matrix multiplication for verification
void matmul_cpu(const float* A, const float* B, float* C, int M, int N, int K) {
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += A[i * K + k] * B[k * N + j];
            }
            C[i * N + j] = sum;
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

TEST_F(MatMulDynamicTest, TiledLeafSmallMatrix) {
    const int M = 64, N = 64, K = 64;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C, *h_ref;
    float *d_A, *d_B, *d_C;

    // Allocate host memory
    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_ref, M * N * sizeof(float)));

    // Allocate device memory
    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));

    // Initialize matrices
    for (int i = 0; i < M * K; i++) h_A[i] = (float)(rand() % 10) / 10.0f;
    for (int i = 0; i < K * N; i++) h_B[i] = (float)(rand() % 10) / 10.0f;

    // Copy to device
    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch kernel
    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    matmul_tiled_leaf<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K, 0, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result back
    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify
    matmul_cpu(h_A, h_B, h_ref, M, N, K);

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_ref[i], 1e-3f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A); cudaFreeHost(h_B); cudaFreeHost(h_C); cudaFreeHost(h_ref);
    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

TEST_F(MatMulDynamicTest, RowDynamicSmallMatrix) {
    const int M = 32, N = 64, K = 48;
    const int BLOCK_SIZE = 256;

    float *h_A, *h_B, *h_C, *h_ref;
    float *d_A, *d_B, *d_C;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_ref, M * N * sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (float)(i % 10);
    for (int i = 0; i < K * N; i++) h_B[i] = (float)(i % 10);

    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch parent kernel
    int blocks = (M + 255) / 256;
    matmul_row_dynamic<BLOCK_SIZE><<<blocks, 256>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify
    matmul_cpu(h_A, h_B, h_ref, M, N, K);

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_ref[i], 1e-2f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A); cudaFreeHost(h_B); cudaFreeHost(h_C); cudaFreeHost(h_ref);
    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

TEST_F(MatMulDynamicTest, AdaptiveSmallMatrix) {
    const int M = 128, N = 128, K = 128;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C, *h_ref;
    float *d_A, *d_B, *d_C;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_ref, M * N * sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));

    // Initialize with known pattern
    for (int i = 0; i < M * K; i++) h_A[i] = 1.0f;
    for (int i = 0; i < K * N; i++) h_B[i] = 1.0f;

    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch adaptive kernel (single parent thread)
    matmul_adaptive_parent<TILE_SIZE><<<1, 1>>>(d_A, d_B, d_C, M, N, K, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    // With all 1s, result should be K (number of elements in dot product)
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], (float)K, 1e-2f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A); cudaFreeHost(h_B); cudaFreeHost(h_C); cudaFreeHost(h_ref);
    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

TEST_F(MatMulDynamicTest, BlockAdaptiveVerySmall) {
    const int M = 32, N = 32, K = 32;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C;
    float *d_A, *d_B, *d_C;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = 2.0f;
    for (int i = 0; i < K * N; i++) h_B[i] = 3.0f;

    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch block adaptive kernel
    dim3 grid(1, 1);
    dim3 block(1, 1);
    matmul_block_adaptive<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K, M, N, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    // Expected: 2.0 * 3.0 * K = 6.0 * 32 = 192.0
    float expected = 2.0f * 3.0f * K;
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected, 1.0f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A); cudaFreeHost(h_B); cudaFreeHost(h_C);
    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}
