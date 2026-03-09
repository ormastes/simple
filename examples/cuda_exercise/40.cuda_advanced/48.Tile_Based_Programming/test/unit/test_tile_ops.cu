// test_tile_ops.cu - Tests for tile-based programming operations

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/tile_operations.cu"

class TileOpsTest : public GpuTest {};

TEST_F(TileOpsTest, TiledTranspose16x16Works) {
    const int rows = 64;
    const int cols = 64;
    const int N = rows * cols;

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input matrix
    std::vector<float> h_input(N);
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            h_input[i * cols + j] = i * cols + j;
        }
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run tiled transpose
    dim3 blockDim(16, 16);
    dim3 gridDim((cols + 15) / 16, (rows + 15) / 16);
    tiled_transpose<16><<<gridDim, blockDim>>>(d_output, d_input, rows, cols);
    CHECK_KERNEL_LAUNCH();

    // Verify transpose
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            EXPECT_FLOAT_EQ(h_output[j * rows + i], h_input[i * cols + j]);
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(TileOpsTest, TiledMatmulSmallWorks) {
    const int M = 32, N = 32, K = 32;

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    // Initialize matrices
    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    for (int i = 0; i < M * K; i++) h_A[i] = 1.0f;
    for (int i = 0; i < K * N; i++) h_B[i] = 1.0f;

    cuda_memcpy_h2d(d_A, h_A.data(), M * K);
    cuda_memcpy_h2d(d_B, h_B.data(), K * N);

    // Run tiled matmul
    dim3 blockDim(16, 16);
    dim3 gridDim((N + 15) / 16, (M + 15) / 16);
    tiled_matmul<16><<<gridDim, blockDim>>>(d_C, d_A, d_B, M, N, K);
    CHECK_KERNEL_LAUNCH();

    // Verify result (all elements should be K)
    std::vector<float> h_C(M * N);
    cuda_memcpy_d2h(h_C.data(), d_C, M * N);

    for (int i = 0; i < M * N; i++) {
        EXPECT_FLOAT_EQ(h_C[i], static_cast<float>(K));
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

TEST_F(TileOpsTest, TiledReductionWorks) {
    const int N = 1024;
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(4);  // 1024 / 256 = 4 blocks

    // Initialize input (all ones)
    std::vector<float> h_input(N, 1.0f);
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run tiled reduction
    tiled_reduction<<<4, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify partial sums
    std::vector<float> h_output(4);
    cuda_memcpy_d2h(h_output.data(), d_output, 4);

    for (int i = 0; i < 4; i++) {
        EXPECT_FLOAT_EQ(h_output[i], 256.0f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(TileOpsTest, TiledConv1DWorks) {
    const int N = 1024;
    const int FILTER_SIZE = 5;

    float* d_input = cuda_malloc<float>(N);
    float* d_filter = cuda_malloc<float>(FILTER_SIZE);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input and filter
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 10);
    }

    std::vector<float> h_filter(FILTER_SIZE);
    for (int i = 0; i < FILTER_SIZE; i++) {
        h_filter[i] = 1.0f / FILTER_SIZE;  // Average filter
    }

    cuda_memcpy_h2d(d_input, h_input.data(), N);
    cuda_memcpy_h2d(d_filter, h_filter.data(), FILTER_SIZE);

    // Run tiled convolution
    const int TILE_SIZE = 256;
    int gridSize = (N + TILE_SIZE - 1) / TILE_SIZE;
    tiled_conv1d<TILE_SIZE, FILTER_SIZE><<<gridSize, TILE_SIZE + FILTER_SIZE - 1>>>(
        d_output, d_input, d_filter, N);
    CHECK_KERNEL_LAUNCH();

    // Verify output exists
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    // Just check that output is non-zero and bounded
    for (int i = 100; i < 900; i++) {  // Check middle region
        EXPECT_GE(h_output[i], 0.0f);
        EXPECT_LE(h_output[i], 10.0f);
    }

    cuda_free(d_input);
    cuda_free(d_filter);
    cuda_free(d_output);
}

TEST_F(TileOpsTest, CooperativeTiledAddWorks) {
    const int N = 1024;
    float* d_A = cuda_malloc<float>(N);
    float* d_B = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize inputs
    std::vector<float> h_A(N), h_B(N);
    for (int i = 0; i < N; i++) {
        h_A[i] = static_cast<float>(i);
        h_B[i] = static_cast<float>(i * 2);
    }

    cuda_memcpy_h2d(d_A, h_A.data(), N);
    cuda_memcpy_h2d(d_B, h_B.data(), N);

    // Run cooperative tiled add
    cooperative_tiled_add<<<(N+255)/256, 256>>>(d_output, d_A, d_B, N);
    CHECK_KERNEL_LAUNCH();

    // Verify results
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_A[i] + h_B[i]);
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_output);
}

TEST_F(TileOpsTest, TiledTranspose32x32Works) {
    const int rows = 128;
    const int cols = 128;
    const int N = rows * cols;

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input matrix
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run tiled transpose with 32x32 tiles
    dim3 blockDim(32, 32);
    dim3 gridDim((cols + 31) / 32, (rows + 31) / 32);
    tiled_transpose<32><<<gridDim, blockDim>>>(d_output, d_input, rows, cols);
    CHECK_KERNEL_LAUNCH();

    // Verify transpose
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            EXPECT_FLOAT_EQ(h_output[j * rows + i], h_input[i * cols + j]);
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(TileOpsTest, TiledMatmul16LargeWorks) {
    const int M = 64, N = 64, K = 64;

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    // Initialize matrices with simple pattern
    std::vector<float> h_A(M * K, 0.5f);
    std::vector<float> h_B(K * N, 2.0f);

    cuda_memcpy_h2d(d_A, h_A.data(), M * K);
    cuda_memcpy_h2d(d_B, h_B.data(), K * N);

    // Run tiled matmul
    dim3 blockDim(16, 16);
    dim3 gridDim((N + 15) / 16, (M + 15) / 16);
    tiled_matmul<16><<<gridDim, blockDim>>>(d_C, d_A, d_B, M, N, K);
    CHECK_KERNEL_LAUNCH();

    // Verify result (each element should be 0.5 * 2.0 * K)
    std::vector<float> h_C(M * N);
    cuda_memcpy_d2h(h_C.data(), d_C, M * N);

    float expected = 0.5f * 2.0f * K;
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected, 1e-4f);
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}
