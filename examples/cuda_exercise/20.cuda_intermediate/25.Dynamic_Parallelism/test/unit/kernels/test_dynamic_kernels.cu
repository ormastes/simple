/**
 * Unit tests for dynamic parallelism kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"

// Include kernels
#include "../../../src/part_specific/dynamic_kernels.cu"

// Test fixture
class DynamicKernelsTest : public GpuTest {
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

    void TearDown() override {
        GpuTest::TearDown();
    }
};

// ============================================================================
// Tests
// ============================================================================

TEST_F(DynamicKernelsTest, QuicksortSmallArray) {
    const int N = 16;  // Small array for testing recursion
    int *h_data, *d_data;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));

    // Initialize with reverse sorted data
    for (int i = 0; i < N; i++) {
        h_data[i] = N - i;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));

    quicksort_dynamic<<<1, 1>>>(d_data, 0, N - 1, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Note: Give extra time for recursive kernels to complete
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_data, d_data, N * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify sorted
    for (int i = 0; i < N - 1; i++) {
        EXPECT_LE(h_data[i], h_data[i + 1]) << "Not sorted at index " << i;
    }

    cudaFreeHost(h_data);
    cudaFree(d_data);
}

TEST_F(DynamicKernelsTest, AdaptiveHistogram) {
    const int N = 1024;
    const int NUM_BINS = 16;
    int *h_data, *h_histogram, *h_expected;
    int *d_data, *d_histogram;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_histogram, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_expected, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_histogram, NUM_BINS * sizeof(int)));

    // Initialize
    for (int i = 0; i < NUM_BINS; i++) h_expected[i] = 0;
    for (int i = 0; i < N; i++) {
        h_data[i] = i % NUM_BINS;
        h_expected[i % NUM_BINS]++;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_histogram, 0, NUM_BINS * sizeof(int)));

    histogram_adaptive<<<1, 1>>>(d_data, d_histogram, N, NUM_BINS, 512);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_histogram, d_histogram, NUM_BINS * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], h_expected[i]) << "Mismatch at bin " << i;
    }

    cudaFreeHost(h_data);
    cudaFreeHost(h_histogram);
    cudaFreeHost(h_expected);
    cudaFree(d_data);
    cudaFree(d_histogram);
}

TEST_F(DynamicKernelsTest, TreeTraversal) {
    const int NUM_NODES = 3;
    TreeNode h_nodes[NUM_NODES] = {
        {0, 1, 2},
        {1, -1, -1},
        {2, -1, -1}
    };

    TreeNode *d_nodes;
    int *d_output, *d_counter;
    int *h_output, h_counter = 0;

    CHECK_CUDA(cudaMalloc(&d_nodes, NUM_NODES * sizeof(TreeNode)));
    CHECK_CUDA(cudaMalloc(&d_output, NUM_NODES * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_counter, sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_output, NUM_NODES * sizeof(int)));

    CHECK_CUDA(cudaMemcpy(d_nodes, h_nodes, NUM_NODES * sizeof(TreeNode), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_counter, &h_counter, sizeof(int), cudaMemcpyHostToDevice));

    tree_traverse<<<1, 1>>>(d_nodes, d_output, 0, d_counter, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(&h_counter, d_counter, sizeof(int), cudaMemcpyDeviceToHost));

    EXPECT_EQ(h_counter, NUM_NODES);

    cudaFreeHost(h_output);
    cudaFree(d_nodes);
    cudaFree(d_output);
    cudaFree(d_counter);
}

TEST_F(DynamicKernelsTest, DynamicWorkGeneration) {
    const int N = 1024;
    int *h_data, *d_data;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));

    for (int i = 0; i < N; i++) {
        h_data[i] = i;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));

    dynamic_work_generator<<<1, 1>>>(d_data, N, 256);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_data, d_data, N * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_data[i], i * 2 + 1) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_data);
    cudaFree(d_data);
}
