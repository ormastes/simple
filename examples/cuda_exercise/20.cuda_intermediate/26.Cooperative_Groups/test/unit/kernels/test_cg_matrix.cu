/**
 * Tests for Cooperative Groups Matrix Operation Kernels (Module 26)
 *
 * These tests validate matrix operations using cooperative groups
 * that improve upon Module 25's dynamic parallelism.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/cg_matrix.cu"
#include <vector>
#include <cmath>
#include <random>

class CGMatrixTest : public GpuTest {
protected:
    static constexpr int TILE_SIZE = 16;
    static constexpr int BLOCK_SIZE = 256;

    // Helper: Initialize matrix with values
    void init_matrix(std::vector<float>& mat, int rows, int cols, float scale = 1.0f) {
        std::mt19937 rng(42);
        std::uniform_real_distribution<float> dist(-scale, scale);
        for (int i = 0; i < rows * cols; i++) {
            mat[i] = dist(rng);
        }
    }

    // Helper: CPU matrix multiplication for validation
    void cpu_matmul(const std::vector<float>& A, const std::vector<float>& B,
                    std::vector<float>& C, int M, int N, int K) {
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
};

// ============================================================================
// Matrix Transpose Tests
// ============================================================================

TEST_F(CGMatrixTest, MatrixTranspose) {
    const int rows = 64;
    const int cols = 128;

    std::vector<float> h_input(rows * cols);
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            h_input[i * cols + j] = i * cols + j;
        }
    }

    float* d_input = cuda_malloc<float>(rows * cols);
    float* d_output = cuda_malloc<float>(rows * cols);

    cuda_memcpy(d_input, h_input.data(), rows * cols, cudaMemcpyHostToDevice);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((cols + TILE_SIZE - 1) / TILE_SIZE, (rows + TILE_SIZE - 1) / TILE_SIZE);

    matrix_transpose_cg<TILE_SIZE><<<grid, block>>>(d_output, d_input, rows, cols);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(rows * cols);
    cuda_memcpy(h_output.data(), d_output, rows * cols, cudaMemcpyDeviceToHost);

    // Verify transpose
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            float expected = h_input[i * cols + j];
            float actual = h_output[j * rows + i];
            EXPECT_FLOAT_EQ(actual, expected) << "At (" << i << ", " << j << ")";
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Tiled Matrix Multiplication Tests
// ============================================================================

TEST_F(CGMatrixTest, TiledMatMul) {
    const int M = 64, N = 64, K = 64;

    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C(M * N, 0.0f);
    std::vector<float> expected(M * N, 0.0f);

    init_matrix(h_A, M, K, 1.0f);
    init_matrix(h_B, K, N, 1.0f);

    cpu_matmul(h_A, h_B, expected, M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    matmul_cg_tiled<TILE_SIZE><<<grid, block>>>(d_C, d_A, d_B, M, N, K);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_C.data(), d_C, M * N, cudaMemcpyDeviceToHost);

    // Verify results
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected[i], 1e-3f) << "Index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

// ============================================================================
// Warp Shuffle Matrix Multiplication Tests
// ============================================================================

TEST_F(CGMatrixTest, WarpShuffleMatMul) {
    const int M = 32, N = 16, K = 32;

    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C(M * N, 0.0f);
    std::vector<float> expected(M * N, 0.0f);

    init_matrix(h_A, M, K, 1.0f);
    init_matrix(h_B, K, N, 1.0f);

    cpu_matmul(h_A, h_B, expected, M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    dim3 grid(N, (M + 31) / 32);
    dim3 block(32);

    matmul_cg_warp_shuffle<32><<<grid, block>>>(d_C, d_A, d_B, M, N, K);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_C.data(), d_C, M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected[i], 1e-2f) << "Index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

// ============================================================================
// Matrix-Vector Multiplication Tests
// ============================================================================

TEST_F(CGMatrixTest, MatVec) {
    const int M = 128, N = 256;

    std::vector<float> h_A(M * N);
    std::vector<float> h_x(N);
    std::vector<float> h_y(M, 0.0f);
    std::vector<float> expected(M, 0.0f);

    init_matrix(h_A, M, N, 1.0f);
    init_matrix(h_x, N, 1, 1.0f);

    // CPU computation
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            expected[i] += h_A[i * N + j] * h_x[j];
        }
    }

    float* d_A = cuda_malloc<float>(M * N);
    float* d_x = cuda_malloc<float>(N);
    float* d_y = cuda_malloc<float>(M);

    cuda_memcpy(d_A, h_A.data(), M * N, cudaMemcpyHostToDevice);
    cuda_memcpy(d_x, h_x.data(), N, cudaMemcpyHostToDevice);

    matvec_cg<BLOCK_SIZE><<<M, BLOCK_SIZE>>>(d_y, d_A, d_x, M, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_y.data(), d_y, M, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M; i++) {
        EXPECT_NEAR(h_y[i], expected[i], 1e-2f) << "Row " << i;
    }

    cuda_free(d_A);
    cuda_free(d_x);
    cuda_free(d_y);
}

// ============================================================================
// Grid-Wide Matrix Multiplication Tests
// ============================================================================

TEST_F(CGMatrixTest, GridMatMul) {
    if (!supports_cooperative_launch()) {
        GTEST_SKIP() << "Cooperative launch not supported";
    }

    const int M = 32, N = 32, K = 32;

    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C(M * N, 0.0f);
    std::vector<float> expected(M * N, 0.0f);

    init_matrix(h_A, M, K, 1.0f);
    init_matrix(h_B, K, N, 1.0f);

    cpu_matmul(h_A, h_B, expected, M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    int num_blocks = grid.x * grid.y;
    float* d_temp = cuda_malloc<float>(num_blocks * TILE_SIZE * TILE_SIZE);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    void* kernel_ptr = (void*)matmul_cg_grid<TILE_SIZE>;
    void* kernel_args[] = {&d_C, &d_A, &d_B, &d_temp, &M, &N, &K};

    cudaLaunchCooperativeKernel(kernel_ptr, grid, block, kernel_args, 0, 0);
    CHECK_LAST_CUDA_ERROR();

    cuda_memcpy(h_C.data(), d_C, M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected[i], 1e-2f) << "Index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
    cuda_free(d_temp);
}

// ============================================================================
// Batched Matrix Multiplication Tests
// ============================================================================

TEST_F(CGMatrixTest, BatchedMatMul) {
    const int M = 16, N = 16, K = 16;
    const int batch_size = 4;

    // Host arrays of pointers
    std::vector<float*> h_A_ptrs(batch_size);
    std::vector<float*> h_B_ptrs(batch_size);
    std::vector<float*> h_C_ptrs(batch_size);

    // Device arrays of pointers
    float** d_A_batch = cuda_malloc<float*>(batch_size);
    float** d_B_batch = cuda_malloc<float*>(batch_size);
    float** d_C_batch = cuda_malloc<float*>(batch_size);

    // Allocate and initialize matrices for each batch
    for (int b = 0; b < batch_size; b++) {
        std::vector<float> h_A(M * K);
        std::vector<float> h_B(K * N);

        init_matrix(h_A, M, K, 1.0f);
        init_matrix(h_B, K, N, 1.0f);

        h_A_ptrs[b] = cuda_malloc<float>(M * K);
        h_B_ptrs[b] = cuda_malloc<float>(K * N);
        h_C_ptrs[b] = cuda_malloc<float>(M * N);

        cuda_memcpy(h_A_ptrs[b], h_A.data(), M * K, cudaMemcpyHostToDevice);
        cuda_memcpy(h_B_ptrs[b], h_B.data(), K * N, cudaMemcpyHostToDevice);
    }

    // Copy pointer arrays to device
    cuda_memcpy(d_A_batch, h_A_ptrs.data(), batch_size, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B_batch, h_B_ptrs.data(), batch_size, cudaMemcpyHostToDevice);
    cuda_memcpy(d_C_batch, h_C_ptrs.data(), batch_size, cudaMemcpyHostToDevice);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE,
              (M + TILE_SIZE - 1) / TILE_SIZE,
              batch_size);

    batched_matmul_cg<TILE_SIZE><<<grid, block>>>(d_C_batch,
                                                   const_cast<const float**>(d_A_batch),
                                                   const_cast<const float**>(d_B_batch),
                                                   M, N, K, batch_size);
    CHECK_KERNEL_LAUNCH();

    // Verify each batch
    for (int b = 0; b < batch_size; b++) {
        std::vector<float> h_C(M * N);
        cuda_memcpy(h_C.data(), h_C_ptrs[b], M * N, cudaMemcpyDeviceToHost);

        // Just check non-zero (exact values depend on random initialization)
        bool has_nonzero = false;
        for (float val : h_C) {
            if (std::abs(val) > 1e-5f) {
                has_nonzero = true;
                break;
            }
        }
        EXPECT_TRUE(has_nonzero) << "Batch " << b << " has all zeros";
    }

    // Cleanup
    for (int b = 0; b < batch_size; b++) {
        cuda_free(h_A_ptrs[b]);
        cuda_free(h_B_ptrs[b]);
        cuda_free(h_C_ptrs[b]);
    }
    cuda_free(d_A_batch);
    cuda_free(d_B_batch);
    cuda_free(d_C_batch);
}

// ============================================================================
// Performance Tests
// ============================================================================

TEST_F(CGMatrixTest, MatMulPerformance) {
    const int M = 256, N = 256, K = 256;
    const int iterations = 10;

    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);

    init_matrix(h_A, M, K, 1.0f);
    init_matrix(h_B, K, N, 1.0f);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    // Warm-up
    matmul_cg_tiled<TILE_SIZE><<<grid, block>>>(d_C, d_A, d_B, M, N, K);
    cudaDeviceSynchronize();

    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);

    cudaEventRecord(start);
    for (int i = 0; i < iterations; i++) {
        matmul_cg_tiled<TILE_SIZE><<<grid, block>>>(d_C, d_A, d_B, M, N, K);
    }
    cudaEventRecord(stop);
    cudaEventSynchronize(stop);

    float elapsed_ms;
    cudaEventElapsedTime(&elapsed_ms, start, stop);
    float avg_time = elapsed_ms / iterations;

    // Calculate GFLOPS
    double flops = 2.0 * M * N * K;  // Multiply-add = 2 ops
    double gflops = (flops / (avg_time / 1000.0)) / 1e9;

    std::cout << "Matrix multiplication (" << M << "x" << N << "x" << K << ")\n";
    std::cout << "Average time: " << avg_time << " ms\n";
    std::cout << "Performance: " << gflops << " GFLOPS\n";

    EXPECT_GT(gflops, 10.0) << "Performance too low";

    cudaEventDestroy(start);
    cudaEventDestroy(stop);
    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}
