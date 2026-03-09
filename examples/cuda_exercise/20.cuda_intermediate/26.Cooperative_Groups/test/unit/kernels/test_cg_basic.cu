/**
 * Basic Tests for Cooperative Groups (Module 26)
 *
 * Tests that mirror Module 25's structure but use cooperative groups.
 * Verifies improvements over dynamic parallelism.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/vector_ops_cg.cu"
#include "kernels/matrix_multiply_cg.cu"
#include "part_specific/cg_kernels.cu"
#include <vector>
#include <numeric>
#include <algorithm>

class CGBasicTest : public GpuTest {
protected:
    static constexpr int BLOCK_SIZE = 256;
    static constexpr int TILE_SIZE = 16;
};

// ============================================================================
// Vector Operations Tests (mirrors Module 25)
// ============================================================================

TEST_F(CGBasicTest, ReductionLeaf) {
    const int N = 1024;
    std::vector<float> h_input(N, 1.0f);

    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
    float* d_output = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    reduction_leaf<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N, 0);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(num_blocks);
    cuda_memcpy(h_output.data(), d_output, num_blocks, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);
    EXPECT_NEAR(result, static_cast<float>(N), 1e-3f);

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(CGBasicTest, DotProduct) {
    const int N = 1024;
    std::vector<float> h_a(N, 2.0f);
    std::vector<float> h_b(N, 3.0f);

    float expected = 2.0f * 3.0f * N;

    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_result = cuda_malloc<float>(1);

    cuda_memcpy(d_a, h_a.data(), N, cudaMemcpyHostToDevice);
    cuda_memcpy(d_b, h_b.data(), N, cudaMemcpyHostToDevice);
    cudaMemset(d_result, 0, sizeof(float));

    int num_blocks = 4;
    dot_product_cg<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_a, d_b, d_result, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_result(1);
    cuda_memcpy(h_result.data(), d_result, 1, cudaMemcpyDeviceToHost);

    EXPECT_NEAR(h_result[0], expected, 1e-2f);

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_result);
}

// ============================================================================
// Matrix Operations Tests (mirrors Module 25)
// ============================================================================

TEST_F(CGBasicTest, MatMulTiled) {
    const int M = 64, N = 64, K = 64;

    std::vector<float> h_A(M * K, 1.0f);
    std::vector<float> h_B(K * N, 1.0f);
    std::vector<float> h_C(M * N, 0.0f);

    float expected = static_cast<float>(K);  // Each element is sum of K 1.0s

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    matmul_adaptive_cg<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_C.data(), d_C, M * N, cudaMemcpyDeviceToHost);

    for (int i = 0; i < 10; i++) {  // Check first 10 elements
        EXPECT_NEAR(h_C[i], expected, 1e-3f) << "Index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

// ============================================================================
// Core Pattern Tests (mirrors Module 25)
// ============================================================================

TEST_F(CGBasicTest, BitonicSort) {
    const int N = 256;
    std::vector<int> h_data(N);

    // Initialize with reverse order
    for (int i = 0; i < N; i++) {
        h_data[i] = N - i;
    }

    int* d_data = cuda_malloc<int>(N);
    cuda_memcpy(d_data, h_data.data(), N, cudaMemcpyHostToDevice);

    bitonic_sort_cg<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_data.data(), d_data, N, cudaMemcpyDeviceToHost);

    // Verify sorted
    for (int i = 1; i < N; i++) {
        EXPECT_LE(h_data[i-1], h_data[i]) << "Not sorted at index " << i;
    }

    cuda_free(d_data);
}

TEST_F(CGBasicTest, HistogramWarpAggregated) {
    const int N = 1024;
    const int NUM_BINS = 256;

    std::vector<int> h_data(N);
    for (int i = 0; i < N; i++) {
        h_data[i] = i % NUM_BINS;
    }

    int* d_data = cuda_malloc<int>(N);
    int* d_histogram = cuda_malloc<int>(NUM_BINS);

    cuda_memcpy(d_data, h_data.data(), N, cudaMemcpyHostToDevice);
    cudaMemset(d_histogram, 0, NUM_BINS * sizeof(int));

    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    histogram_warp_aggregated<BLOCK_SIZE, NUM_BINS><<<num_blocks, BLOCK_SIZE>>>(d_data, d_histogram, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_histogram(NUM_BINS);
    cuda_memcpy(h_histogram.data(), d_histogram, NUM_BINS, cudaMemcpyDeviceToHost);

    // Each bin should have N/NUM_BINS elements
    int expected = N / NUM_BINS;
    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], expected) << "Bin " << i;
    }

    cuda_free(d_data);
    cuda_free(d_histogram);
}
