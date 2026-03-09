/**
 * Cooperative Groups Tests (Module 23 + Module 25 Enhanced)
 *
 * Comprehensive test suite for all cooperative groups kernels.
 * Tests correctness, performance, and edge cases.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "cooperative_groups_kernels.h"

#include <vector>
#include <numeric>
#include <algorithm>
#include <cmath>

// ============================================================================
// Test Fixture
// ============================================================================

class CooperativeGroupsTest : public GpuTest {
protected:
    static constexpr int BLOCK_SIZE = 256;
    static constexpr float EPSILON = 1e-4f;

    // Helper: Verify reduction result
    void VerifyReduction(const std::vector<float>& input, float result) {
        float expected = std::accumulate(input.begin(), input.end(), 0.0f);
        EXPECT_NEAR(result, expected, EPSILON * input.size());
    }

    // Helper: Verify scan result (inclusive)
    void VerifyScanInclusive(const std::vector<float>& input,
                              const std::vector<float>& output) {
        ASSERT_EQ(input.size(), output.size());

        float running_sum = 0.0f;
        for (size_t i = 0; i < input.size(); i++) {
            running_sum += input[i];
            EXPECT_NEAR(output[i], running_sum, EPSILON * (i + 1))
                << "Mismatch at index " << i;
        }
    }

    // Helper: Verify scan result (exclusive)
    void VerifyScanExclusive(const std::vector<float>& input,
                              const std::vector<float>& output) {
        ASSERT_EQ(input.size(), output.size());

        float running_sum = 0.0f;
        for (size_t i = 0; i < input.size(); i++) {
            EXPECT_NEAR(output[i], running_sum, EPSILON * (i + 1))
                << "Mismatch at index " << i;
            running_sum += input[i];
        }
    }
};

// ============================================================================
// Reduction Tests
// ============================================================================

TEST_F(CooperativeGroupsTest, ThreadBlockReductionSmall) {
    const int N = 1024;

    std::vector<float> h_input(N, 1.0f);  // All ones
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(1);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float* d_partial = cuda_malloc<float>(grid_size);

    reduction_cg_thread_block<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_partial, N);
    CHECK_KERNEL_LAUNCH();

    // Second reduction to get final result
    reduction_cg_thread_block<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(
        d_partial, d_output, grid_size);
    CHECK_KERNEL_LAUNCH();

    float result;
    cuda_memcpy(&result, d_output, 1, cudaMemcpyDeviceToHost);

    EXPECT_NEAR(result, static_cast<float>(N), EPSILON * N);

    cuda_free(d_input);
    cuda_free(d_output);
    cuda_free(d_partial);
}

TEST_F(CooperativeGroupsTest, TiledReductionWithShuffles) {
    const int N = 4096;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100);
    }

    float* d_input = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    int grid_size = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
    float* d_output = cuda_malloc<float>(grid_size);

    reduction_cg_tiled<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    // Reduce partial results on CPU
    std::vector<float> h_output(grid_size);
    cuda_memcpy(h_output.data(), d_output, grid_size, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    VerifyReduction(h_input, result);

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(CooperativeGroupsTest, CoalescedReductionWithDivergence) {
    const int N = 2048;
    const int threshold = 50;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100);
    }

    float* d_input = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float* d_output = cuda_malloc<float>(grid_size);

    reduction_cg_coalesced<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_output, N, threshold);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(grid_size);
    cuda_memcpy(h_output.data(), d_output, grid_size, cudaMemcpyDeviceToHost);

    float gpu_result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    // Compute expected result with same threshold logic
    float expected = 0.0f;
    for (int i = 0; i < N; i++) {
        float val = h_input[i];
        expected += (val > threshold) ? val * 2.0f : val * 0.5f;
    }

    EXPECT_NEAR(gpu_result, expected, EPSILON * N);

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(CooperativeGroupsTest, HierarchicalReductionMultipleTileSizes) {
    const int N = 8192;

    std::vector<float> h_input(N, 2.5f);

    float* d_input = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    auto test_tile_size = [&](int tile_size, auto kernel) {
        int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
        float* d_output = cuda_malloc<float>(grid_size);

        kernel<<<grid_size, BLOCK_SIZE>>>(d_input, d_output, N);
        CHECK_KERNEL_LAUNCH();

        std::vector<float> h_output(grid_size);
        cuda_memcpy(h_output.data(), d_output, grid_size, cudaMemcpyDeviceToHost);

        float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);
        float expected = 2.5f * N;

        EXPECT_NEAR(result, expected, EPSILON * N)
            << "Failed for tile size " << tile_size;

        cuda_free(d_output);
    };

    test_tile_size(4, reduction_cg_hierarchical<BLOCK_SIZE, 4>);
    test_tile_size(8, reduction_cg_hierarchical<BLOCK_SIZE, 8>);
    test_tile_size(16, reduction_cg_hierarchical<BLOCK_SIZE, 16>);
    test_tile_size(32, reduction_cg_hierarchical<BLOCK_SIZE, 32>);

    cuda_free(d_input);
}

// ============================================================================
// Histogram Tests
// ============================================================================

TEST_F(CooperativeGroupsTest, HistogramWarpAggregated) {
    const int N = 10000;
    const int NUM_BINS = 256;

    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = i % NUM_BINS;
    }

    int* d_input = cuda_malloc<int>(N);
    int* d_histogram = cuda_malloc<int>(NUM_BINS);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));
    cuda_memset(d_histogram, 0, NUM_BINS * sizeof(int));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    histogram_cg_warp_aggregated<BLOCK_SIZE, NUM_BINS><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_histogram, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_histogram(NUM_BINS);
    cuda_memcpy(h_histogram.data(), d_histogram, NUM_BINS, cudaMemcpyDeviceToHost);

    // Verify: each bin should have N / NUM_BINS elements
    int expected_per_bin = N / NUM_BINS;
    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], expected_per_bin)
            << "Bin " << i << " has incorrect count";
    }

    cuda_free(d_input);
    cuda_free(d_histogram);
}

TEST_F(CooperativeGroupsTest, HistogramLabeled) {
    const int N = 5000;
    const int NUM_BINS = 128;

    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = (i * 7) % NUM_BINS;  // Prime pattern
    }

    int* d_input = cuda_malloc<int>(N);
    int* d_histogram = cuda_malloc<int>(NUM_BINS);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));
    cuda_memset(d_histogram, 0, NUM_BINS * sizeof(int));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    histogram_cg_labeled<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_histogram, N, NUM_BINS);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_histogram(NUM_BINS);
    cuda_memcpy(h_histogram.data(), d_histogram, NUM_BINS, cudaMemcpyDeviceToHost);

    // Verify total count
    int total = std::accumulate(h_histogram.begin(), h_histogram.end(), 0);
    EXPECT_EQ(total, N);

    // Verify each bin has correct count
    std::vector<int> expected_hist(NUM_BINS, 0);
    for (int val : h_input) {
        expected_hist[val]++;
    }

    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], expected_hist[i])
            << "Mismatch at bin " << i;
    }

    cuda_free(d_input);
    cuda_free(d_histogram);
}

// ============================================================================
// Scan (Prefix Sum) Tests
// ============================================================================

TEST_F(CooperativeGroupsTest, ScanInclusiveSmall) {
    const int N = 512;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    scan_cg_inclusive<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_output, nullptr, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(N);
    cuda_memcpy(h_output.data(), d_output, N, cudaMemcpyDeviceToHost);

    // For all ones, inclusive scan should be [1, 2, 3, ..., N]
    for (int i = 0; i < N; i++) {
        float expected = static_cast<float>(i + 1);
        EXPECT_NEAR(h_output[i], expected, EPSILON * (i + 1))
            << "Mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(CooperativeGroupsTest, ScanExclusiveSmall) {
    const int N = 768;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 10);
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    scan_cg_exclusive<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(N);
    cuda_memcpy(h_output.data(), d_output, N, cudaMemcpyDeviceToHost);

    VerifyScanExclusive(h_input, h_output);

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Bitonic Sort Tests
// ============================================================================

TEST_F(CooperativeGroupsTest, BitonicSortSingleBlock) {
    const int N = BLOCK_SIZE;

    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = N - i - 1;  // Reverse order
    }

    int* d_data = cuda_malloc<int>(N);
    cuda_memcpy(d_data, h_input.data(), N, cudaMemcpyHostToDevice);

    bitonic_sort_cg<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_output(N);
    cuda_memcpy(h_output.data(), d_data, N, cudaMemcpyDeviceToHost);

    // Verify sorted
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], i) << "Not sorted at index " << i;
    }

    cuda_free(d_data);
}

TEST_F(CooperativeGroupsTest, BitonicSortRandomData) {
    const int N = BLOCK_SIZE;

    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = (i * 17 + 13) % N;  // Pseudo-random
    }

    int* d_data = cuda_malloc<int>(N);
    cuda_memcpy(d_data, h_input.data(), N, cudaMemcpyHostToDevice);

    bitonic_sort_cg<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_output(N);
    cuda_memcpy(h_output.data(), d_data, N, cudaMemcpyDeviceToHost);

    // Verify sorted
    for (int i = 1; i < N; i++) {
        EXPECT_LE(h_output[i-1], h_output[i])
            << "Not sorted: h_output[" << i-1 << "] = " << h_output[i-1]
            << " > h_output[" << i << "] = " << h_output[i];
    }

    cuda_free(d_data);
}

// ============================================================================
// Matrix Operations Tests
// ============================================================================

TEST_F(CooperativeGroupsTest, MatrixTransposeSquare) {
    const int SIZE = 32;
    const int N = SIZE * SIZE;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    dim3 grid((SIZE + 15) / 16, (SIZE + 15) / 16);
    dim3 block(16, 16);

    matrix_transpose_cg<16><<<grid, block>>>(d_input, d_output, SIZE, SIZE);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(N);
    cuda_memcpy(h_output.data(), d_output, N, cudaMemcpyDeviceToHost);

    // Verify transpose
    for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
            int input_idx = row * SIZE + col;
            int output_idx = col * SIZE + row;
            EXPECT_FLOAT_EQ(h_output[output_idx], h_input[input_idx])
                << "Transpose error at (" << row << ", " << col << ")";
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(CooperativeGroupsTest, MatrixMultiplySmall) {
    const int M = 64, N = 64, K = 64;
    const int TILE_SIZE = 16;

    std::vector<float> h_A(M * K, 1.0f);
    std::vector<float> h_B(K * N, 2.0f);
    std::vector<float> h_C(M * N, 0.0f);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cuda_memcpy(d_A, h_A.data(), M * K, cudaMemcpyHostToDevice);
    cuda_memcpy(d_B, h_B.data(), K * N, cudaMemcpyHostToDevice);

    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);
    dim3 block(TILE_SIZE, TILE_SIZE);

    matrix_multiply_cg<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy(h_C.data(), d_C, M * N, cudaMemcpyDeviceToHost);

    // Each element should be K * 1.0 * 2.0 = 2*K
    float expected = static_cast<float>(K) * 2.0f;
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], expected, EPSILON * K)
            << "Error at index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

// ============================================================================
// Dot Product Test
// ============================================================================

TEST_F(CooperativeGroupsTest, DotProductLarge) {
    const int N = 16384;

    std::vector<float> h_a(N);
    std::vector<float> h_b(N);

    for (int i = 0; i < N; i++) {
        h_a[i] = static_cast<float>(i % 100) / 100.0f;
        h_b[i] = static_cast<float>((i * 3) % 100) / 100.0f;
    }

    float* d_a = cuda_malloc<float>(N);
    float* d_b = cuda_malloc<float>(N);
    float* d_result = cuda_malloc<float>(1);

    cuda_memcpy(d_a, h_a.data(), N, cudaMemcpyHostToDevice);
    cuda_memcpy(d_b, h_b.data(), N, cudaMemcpyHostToDevice);
    cuda_memset(d_result, 0, sizeof(float));

    int grid_size = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    dot_product_cg<BLOCK_SIZE><<<grid_size, BLOCK_SIZE>>>(
        d_a, d_b, d_result, N);
    CHECK_KERNEL_LAUNCH();

    float gpu_result;
    cuda_memcpy(&gpu_result, d_result, 1, cudaMemcpyDeviceToHost);

    // Compute expected on CPU
    float expected = 0.0f;
    for (int i = 0; i < N; i++) {
        expected += h_a[i] * h_b[i];
    }

    EXPECT_NEAR(gpu_result, expected, EPSILON * N);

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_result);
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
