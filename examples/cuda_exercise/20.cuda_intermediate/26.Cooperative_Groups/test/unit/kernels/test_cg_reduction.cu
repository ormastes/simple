/**
 * Tests for Cooperative Groups Reduction Kernels (Module 26)
 *
 * These tests validate the reduction implementations that improve upon
 * Module 25's dynamic parallelism with cooperative groups.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/cg_reduction.cu"
#include <vector>
#include <numeric>
#include <cmath>

class CGReductionTest : public GpuTest {
protected:
    static constexpr int N = 1024 * 1024;  // 1M elements
    static constexpr int BLOCK_SIZE = 256;
};

// ============================================================================
// Thread Block Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, ThreadBlockReduction) {
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }

    float expected = static_cast<float>(N);

    // Allocate device memory
    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
    float* d_output = cuda_malloc<float>(num_blocks);

    // Copy input
    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    // Launch kernel
    reduction_cg_thread_block<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    // Reduce block results on CPU
    std::vector<float> h_output(num_blocks);
    cuda_memcpy(h_output.data(), d_output, num_blocks, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    EXPECT_NEAR(result, expected, 1e-3f);

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Tiled (Shuffle) Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, TiledShuffleReduction) {
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100);
    }

    float expected = std::accumulate(h_input.begin(), h_input.end(), 0.0f);

    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
    float* d_output = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    reduction_cg_tiled<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(num_blocks);
    cuda_memcpy(h_output.data(), d_output, num_blocks, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    EXPECT_NEAR(result, expected, expected * 1e-5f);

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Coalesced Threads Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, CoalescedReduction) {
    const int threshold = 50;
    std::vector<float> h_input(N);

    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i % 100);
    }

    // Compute expected with same logic as kernel
    float expected = 0.0f;
    for (int i = 0; i < N; i++) {
        float val = h_input[i];
        if (val > threshold) {
            expected += val * 2.0f;
        } else {
            expected += val * 0.5f;
        }
    }

    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float* d_output = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    reduction_cg_coalesced<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N, threshold);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(num_blocks);
    cuda_memcpy(h_output.data(), d_output, num_blocks, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    EXPECT_NEAR(result, expected, expected * 1e-4f);

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Grid-Wide Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, GridWideReduction) {
    const int test_size = 1024 * 64;  // Smaller for cooperative launch
    std::vector<float> h_data(test_size);

    for (int i = 0; i < test_size; i++) {
        h_data[i] = 1.0f;
    }

    float expected = static_cast<float>(test_size);

    float* d_data = cuda_malloc<float>(test_size);
    int num_blocks = (test_size + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float* d_temp = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_data, h_data.data(), test_size, cudaMemcpyHostToDevice);

    // Check if cooperative launch is supported
    if (supports_cooperative_launch()) {
        // Get max cooperative blocks
        void* kernel_ptr = (void*)reduction_cg_grid<BLOCK_SIZE>;
        int max_blocks = get_max_cooperative_blocks(0, kernel_ptr, BLOCK_SIZE, 0);
        num_blocks = std::min(num_blocks, max_blocks);

        // Launch cooperative kernel
        void* kernel_args[] = {&d_data, &d_temp, &test_size};
        dim3 block(BLOCK_SIZE);
        dim3 grid(num_blocks);

        cudaLaunchCooperativeKernel(kernel_ptr, grid, block, kernel_args, 0, 0);
        CHECK_LAST_CUDA_ERROR();

        std::vector<float> h_result(1);
        cuda_memcpy(h_result.data(), d_data, 1, cudaMemcpyDeviceToHost);

        EXPECT_NEAR(h_result[0], expected, 1e-3f);
    } else {
        GTEST_SKIP() << "Cooperative launch not supported on this device";
    }

    cuda_free(d_data);
    cuda_free(d_temp);
}

// ============================================================================
// Segmented Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, SegmentedReduction) {
    const int num_segments = 4;
    const int segment_size = 256;
    const int total_size = num_segments * segment_size;

    std::vector<float> h_input(total_size);
    std::vector<int> h_segment_ids(total_size);
    std::vector<int> h_segment_offsets(num_segments);

    // Initialize segments
    for (int seg = 0; seg < num_segments; seg++) {
        h_segment_offsets[seg] = seg * segment_size;
        for (int i = 0; i < segment_size; i++) {
            int idx = seg * segment_size + i;
            h_input[idx] = 1.0f;
            h_segment_ids[idx] = seg;
        }
    }

    std::vector<float> expected(num_segments, static_cast<float>(segment_size));

    float* d_input = cuda_malloc<float>(total_size);
    int* d_segment_ids = cuda_malloc<int>(total_size);
    int* d_segment_offsets = cuda_malloc<int>(num_segments);
    float* d_output = cuda_malloc<float>(num_segments);

    cuda_memcpy(d_input, h_input.data(), total_size, cudaMemcpyHostToDevice);
    cuda_memcpy(d_segment_ids, h_segment_ids.data(), total_size, cudaMemcpyHostToDevice);
    cuda_memcpy(d_segment_offsets, h_segment_offsets.data(), num_segments, cudaMemcpyHostToDevice);
    cudaMemset(d_output, 0, num_segments * sizeof(float));

    int num_blocks = (total_size + BLOCK_SIZE - 1) / BLOCK_SIZE;
    reduction_cg_segmented<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(
        d_input, d_output, d_segment_ids, d_segment_offsets, num_segments, total_size);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(num_segments);
    cuda_memcpy(h_output.data(), d_output, num_segments, cudaMemcpyDeviceToHost);

    for (int i = 0; i < num_segments; i++) {
        EXPECT_NEAR(h_output[i], expected[i], 1e-3f) << "Segment " << i;
    }

    cuda_free(d_input);
    cuda_free(d_segment_ids);
    cuda_free(d_segment_offsets);
    cuda_free(d_output);
}

// ============================================================================
// Hierarchical Reduction Tests
// ============================================================================

TEST_F(CGReductionTest, HierarchicalReduction) {
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }

    float expected = static_cast<float>(N);

    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    float* d_output = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    reduction_cg_hierarchical<BLOCK_SIZE, 4><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(num_blocks);
    cuda_memcpy(h_output.data(), d_output, num_blocks, cudaMemcpyDeviceToHost);

    float result = std::accumulate(h_output.begin(), h_output.end(), 0.0f);

    EXPECT_NEAR(result, expected, 1e-3f);

    cuda_free(d_input);
    cuda_free(d_output);
}

// ============================================================================
// Performance Comparison Tests
// ============================================================================

TEST_F(CGReductionTest, PerformanceComparison) {
    const int iterations = 10;
    std::vector<float> h_input(N, 1.0f);

    float* d_input = cuda_malloc<float>(N);
    int num_blocks = (N + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
    float* d_output = cuda_malloc<float>(num_blocks);

    cuda_memcpy(d_input, h_input.data(), N, cudaMemcpyHostToDevice);

    // Warm-up
    reduction_cg_tiled<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    cudaDeviceSynchronize();

    // Timed run
    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);

    cudaEventRecord(start);
    for (int i = 0; i < iterations; i++) {
        reduction_cg_tiled<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    }
    cudaEventRecord(stop);
    cudaEventSynchronize(stop);

    float elapsed_ms;
    cudaEventElapsedTime(&elapsed_ms, start, stop);
    float avg_time = elapsed_ms / iterations;

    // Calculate bandwidth
    float bytes = N * sizeof(float);
    float bandwidth_gb = (bytes / (avg_time / 1000.0f)) / 1e9f;

    std::cout << "Average reduction time: " << avg_time << " ms\n";
    std::cout << "Bandwidth: " << bandwidth_gb << " GB/s\n";

    // Expect reasonable performance (> 100 GB/s on modern GPUs)
    EXPECT_GT(bandwidth_gb, 50.0f) << "Reduction bandwidth is too low";

    cudaEventDestroy(start);
    cudaEventDestroy(stop);
    cuda_free(d_input);
    cuda_free(d_output);
}
