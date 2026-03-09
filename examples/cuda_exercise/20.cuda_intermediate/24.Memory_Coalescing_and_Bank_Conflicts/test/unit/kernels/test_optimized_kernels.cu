/**
 * Unit tests for Module 24 optimized kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"

// Include improved kernels (Module 24 versions)
#include "../../../src/kernels/matrix_multiply.cu"
#include "../../../src/kernels/vector_ops.cu"

#define TILE_SIZE 16

// Test fixture
class OptimizedKernelsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

// ============================================================================
// Matrix Multiplication Tests
// ============================================================================

TEST_F(OptimizedKernelsTest, MatMulCoalescingOptimized) {
    const int M = 128, N = 128, K = 128;
    float *h_A, *h_B, *h_C, *h_C_ref;
    float *d_A, *d_B, *d_C;

    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, M * N * sizeof(float)));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (i % 10) * 0.1f;
    for (int i = 0; i < K * N; i++) h_B[i] = (i % 10) * 0.1f;

    // Compute reference
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += h_A[i * K + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    matmul_coalescing_optimized<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C);
    cudaFreeHost(h_C_ref);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

TEST_F(OptimizedKernelsTest, MatMulPrefetchDoubleBuffer) {
    const int M = 64, N = 64, K = 64;
    float *h_A, *h_B, *h_C, *h_C_ref;
    float *d_A, *d_B, *d_C;

    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, M * N * sizeof(float)));

    for (int i = 0; i < M * K; i++) h_A[i] = (i % 7) * 0.1f;
    for (int i = 0; i < K * N; i++) h_B[i] = (i % 7) * 0.1f;

    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += h_A[i * K + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    matmul_prefetch_double_buffer<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C);
    cudaFreeHost(h_C_ref);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

// ============================================================================
// Reduction Tests
// ============================================================================

TEST_F(OptimizedKernelsTest, ReductionVectorized) {
    const int N = 1024 * 256;
    const int BLOCK_SIZE = 256;
    float *h_input, *h_output;
    float *d_input, *d_output;

    int num_blocks = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, num_blocks * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, num_blocks * sizeof(float)));

    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    reduction_vectorized<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, num_blocks * sizeof(float), cudaMemcpyDeviceToHost));

    float result = 0.0f;
    for (int i = 0; i < num_blocks; i++) {
        result += h_output[i];
    }

    EXPECT_NEAR(result, static_cast<float>(N), N * 1e-5f);

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(OptimizedKernelsTest, ReductionWarpShuffle) {
    const int N = 1024 * 256;
    const int BLOCK_SIZE = 256;
    float *h_input, *h_output;
    float *d_input, *d_output;

    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, num_blocks * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, num_blocks * sizeof(float)));

    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    reduction_warp_shuffle<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, num_blocks * sizeof(float), cudaMemcpyDeviceToHost));

    float result = 0.0f;
    for (int i = 0; i < num_blocks; i++) {
        result += h_output[i];
    }

    EXPECT_NEAR(result, static_cast<float>(N), N * 1e-5f);

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}

// ============================================================================
// Scan Tests
// ============================================================================

TEST_F(OptimizedKernelsTest, ScanBlelloch) {
    const int N = 512;
    const int BLOCK_SIZE = 256;
    float *h_input, *h_output, *h_expected;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_expected, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, N * sizeof(float)));

    // Initialize
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }

    // Compute expected (inclusive scan)
    h_expected[0] = 0.0f;
    for (int i = 1; i < N; i++) {
        h_expected[i] = h_expected[i - 1] + h_input[i - 1];
    }

    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    int num_blocks = (N + 2 * BLOCK_SIZE - 1) / (2 * BLOCK_SIZE);
    scan_blelloch<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify first block
    for (int i = 0; i < min(N, 2 * BLOCK_SIZE); i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_expected[i]) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFreeHost(h_expected);
    cudaFree(d_input);
    cudaFree(d_output);
}
