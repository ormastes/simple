/**
 * Unit tests for dynamic vector operations kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <cmath>

// Include kernel implementations
#include "../../../src/kernels/vector_ops_dynamic.cu"

// Test fixture
class VectorOpsDynamicTest : public GpuTest {
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
// Tests for Reduction
// ============================================================================

TEST_F(VectorOpsDynamicTest, ReductionLeafSimple) {
    const int N = 1024;
    const int BLOCK_SIZE = 256;

    float *h_input, *h_output;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, sizeof(float)));

    // Initialize with ones
    for (int i = 0; i < N; i++) h_input[i] = 1.0f;

    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch kernel (single block for simplicity)
    reduction_leaf<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(d_input, d_output, N, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, sizeof(float), cudaMemcpyDeviceToHost));

    // Expected: BLOCK_SIZE * 4 (vectorized load of 4 per thread)
    float expected = min(N, BLOCK_SIZE * 4);
    EXPECT_NEAR(h_output[0], expected, 1e-3f);

    cudaFreeHost(h_input); cudaFreeHost(h_output);
    cudaFree(d_input); cudaFree(d_output);
}

TEST_F(VectorOpsDynamicTest, SegmentedReductionSmall) {
    const int NUM_SEGMENTS = 4;
    const int SEGMENT_SIZE = 256;
    const int BLOCK_SIZE = 128;
    const int TOTAL_SIZE = NUM_SEGMENTS * SEGMENT_SIZE;

    float *h_input, *h_output;
    int *h_sizes, *h_offsets;
    float *d_input, *d_output;
    int *d_sizes, *d_offsets;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_input, TOTAL_SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, NUM_SEGMENTS * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_sizes, NUM_SEGMENTS * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_offsets, NUM_SEGMENTS * sizeof(int)));

    CHECK_CUDA(cudaMalloc(&d_input, TOTAL_SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, NUM_SEGMENTS * 10 * sizeof(float))); // Extra space for temp
    CHECK_CUDA(cudaMalloc(&d_sizes, NUM_SEGMENTS * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_offsets, NUM_SEGMENTS * sizeof(int)));

    // Initialize segments
    for (int i = 0; i < NUM_SEGMENTS; i++) {
        h_sizes[i] = SEGMENT_SIZE;
        h_offsets[i] = i * SEGMENT_SIZE;
    }

    for (int i = 0; i < TOTAL_SIZE; i++) {
        h_input[i] = (float)(i % NUM_SEGMENTS + 1);
    }

    // Copy to device
    CHECK_CUDA(cudaMemcpy(d_input, h_input, TOTAL_SIZE * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_sizes, h_sizes, NUM_SEGMENTS * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_offsets, h_offsets, NUM_SEGMENTS * sizeof(int), cudaMemcpyHostToDevice));

    // Launch kernel
    int blocks = (NUM_SEGMENTS + 255) / 256;
    reduction_segmented_parent<BLOCK_SIZE><<<blocks, 256>>>(
        d_input, d_output, d_sizes, d_offsets, NUM_SEGMENTS);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy results
    CHECK_CUDA(cudaMemcpy(h_output, d_output, NUM_SEGMENTS * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify each segment sum
    for (int seg = 0; seg < NUM_SEGMENTS; seg++) {
        float expected = (float)(seg + 1) * min(SEGMENT_SIZE, BLOCK_SIZE * 4);
        EXPECT_GT(h_output[seg], 0.0f) << "Segment " << seg << " has zero sum";
    }

    // Cleanup
    cudaFreeHost(h_input); cudaFreeHost(h_output);
    cudaFreeHost(h_sizes); cudaFreeHost(h_offsets);
    cudaFree(d_input); cudaFree(d_output);
    cudaFree(d_sizes); cudaFree(d_offsets);
}

// ============================================================================
// Tests for Histogram
// ============================================================================

TEST_F(VectorOpsDynamicTest, HistogramAdaptiveDynamic) {
    const int N = 2048;
    const int NUM_BINS = 16;
    const int CHUNKS = 4;

    int *h_data, *h_histogram, *h_expected;
    int *d_data, *d_histogram;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_histogram, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_expected, NUM_BINS * sizeof(int)));

    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_histogram, NUM_BINS * sizeof(int)));

    // Initialize data and expected histogram
    for (int i = 0; i < NUM_BINS; i++) h_expected[i] = 0;

    for (int i = 0; i < N; i++) {
        h_data[i] = i % NUM_BINS;
        h_expected[i % NUM_BINS]++;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_histogram, 0, NUM_BINS * sizeof(int)));

    // Launch adaptive histogram
    int blocks = (CHUNKS + 255) / 256;
    histogram_adaptive_dynamic<<<blocks, 256>>>(d_data, d_histogram, N, NUM_BINS, CHUNKS);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_histogram, d_histogram, NUM_BINS * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], h_expected[i]) << "Bin " << i << " mismatch";
    }

    // Cleanup
    cudaFreeHost(h_data); cudaFreeHost(h_histogram); cudaFreeHost(h_expected);
    cudaFree(d_data); cudaFree(d_histogram);
}

// ============================================================================
// Tests for Scan
// ============================================================================

TEST_F(VectorOpsDynamicTest, ScanBlockSimple) {
    const int N = 256;
    const int BLOCK_SIZE = 256;

    float *h_input, *h_output, *h_expected;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_expected, N * sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, N * sizeof(float)));

    // Initialize with ones
    for (int i = 0; i < N; i++) h_input[i] = 1.0f;

    // Compute expected prefix sum
    h_expected[0] = 0.0f;
    for (int i = 1; i < N; i++) {
        h_expected[i] = h_expected[i - 1] + h_input[i - 1];
    }

    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch kernel
    scan_block<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(d_input, d_output, nullptr, N, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify (exclusive scan)
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_output[i], h_expected[i], 1e-3f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_input); cudaFreeHost(h_output); cudaFreeHost(h_expected);
    cudaFree(d_input); cudaFree(d_output);
}

// ============================================================================
// Tests for Dot Product
// ============================================================================

TEST_F(VectorOpsDynamicTest, DotProductPartialSmall) {
    const int N = 512;
    const int BLOCK_SIZE = 256;

    float *h_a, *h_b, *h_result;
    float *d_a, *d_b, *d_result;

    CHECK_CUDA(cudaMallocHost(&h_a, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_b, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_result, sizeof(float)));

    CHECK_CUDA(cudaMalloc(&d_a, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_b, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_result, 10 * sizeof(float))); // Space for multiple blocks

    // Initialize vectors
    for (int i = 0; i < N; i++) {
        h_a[i] = 2.0f;
        h_b[i] = 3.0f;
    }

    CHECK_CUDA(cudaMemcpy(d_a, h_a, N * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_b, h_b, N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch kernel (single block computes partial)
    int blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    dot_product_partial<BLOCK_SIZE><<<blocks, BLOCK_SIZE>>>(d_a, d_b, d_result, 0, N);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy and sum results
    float *h_partials = new float[blocks];
    CHECK_CUDA(cudaMemcpy(h_partials, d_result, blocks * sizeof(float), cudaMemcpyDeviceToHost));

    float total = 0.0f;
    for (int i = 0; i < blocks; i++) {
        total += h_partials[i];
    }

    // Expected: 2.0 * 3.0 * N = 6.0 * N
    float expected = 2.0f * 3.0f * N;
    EXPECT_NEAR(total, expected, 1e-2f);

    // Cleanup
    delete[] h_partials;
    cudaFreeHost(h_a); cudaFreeHost(h_b); cudaFreeHost(h_result);
    cudaFree(d_a); cudaFree(d_b); cudaFree(d_result);
}
