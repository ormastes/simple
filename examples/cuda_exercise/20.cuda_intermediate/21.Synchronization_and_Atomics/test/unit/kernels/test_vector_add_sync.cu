/**
 * Unit tests for synchronization-optimized vector operations
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"  // From GTestBasicLib, via CMake
#include "kernels/vector_add_sync.cu"

#include <cfloat>
#include <algorithm>

// Test fixture using GpuTest base class
class VectorAddSyncTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        N = 1024;
        size = N * sizeof(float);

        h_a = (float*)malloc(size);
        h_b = (float*)malloc(size);
        h_result = (float*)malloc(size);

        // Initialize vectors
        for (int i = 0; i < N; i++) {
            h_a[i] = (float)i * 0.1f;
            h_b[i] = (float)(i % 100) * 0.01f;
        }

        CHECK_CUDA(cudaMalloc(&d_a, size));
        CHECK_CUDA(cudaMalloc(&d_b, size));
        CHECK_CUDA(cudaMalloc(&d_result, size));

        CHECK_CUDA(cudaMemcpy(d_a, h_a, size, cudaMemcpyHostToDevice));
        CHECK_CUDA(cudaMemcpy(d_b, h_b, size, cudaMemcpyHostToDevice));
    }

    void TearDown() override {
        free(h_a);
        free(h_b);
        free(h_result);
        cudaFree(d_a);
        cudaFree(d_b);
        cudaFree(d_result);

        GpuTest::TearDown();
    }

    int N;
    size_t size;
    float *h_a, *h_b, *h_result;
    float *d_a, *d_b, *d_result;
};

TEST_F(VectorAddSyncTest, WarpShuffleReduction) {
    float expected_sum = 0.0f;
    for (int i = 0; i < N; i++) {
        expected_sum += h_a[i];
    }

    float* d_sum;
    CHECK_CUDA(cudaMalloc(&d_sum, sizeof(float)));
    CHECK_CUDA(cudaMemset(d_sum, 0, sizeof(float)));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    vector_sum_warp_shuffle<<<grid, block>>>(d_a, d_sum, N);
    CHECK_KERNEL_LAUNCH();

    float h_sum;
    CHECK_CUDA(cudaMemcpy(&h_sum, d_sum, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_NEAR(h_sum, expected_sum, 1e-1f);

    cudaFree(d_sum);
}

TEST_F(VectorAddSyncTest, AtomicHistogram) {
    const int num_bins = 10;
    int* h_input = new int[N];
    int* h_histogram = new int[num_bins];
    int* expected_histogram = new int[num_bins];

    // Initialize input and expected histogram
    memset(expected_histogram, 0, num_bins * sizeof(int));
    for (int i = 0; i < N; i++) {
        h_input[i] = i % num_bins;
        expected_histogram[h_input[i]]++;
    }

    int* d_input;
    int* d_histogram;
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_histogram, num_bins * sizeof(int)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_histogram, 0, num_bins * sizeof(int)));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);
    size_t shared_size = num_bins * sizeof(int);

    vector_histogram_atomic<<<grid, block, shared_size>>>(d_input, d_histogram, N, num_bins);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_histogram, d_histogram, num_bins * sizeof(int), cudaMemcpyDeviceToHost));

    for (int i = 0; i < num_bins; i++) {
        EXPECT_EQ(h_histogram[i], expected_histogram[i]);
    }

    delete[] h_input;
    delete[] h_histogram;
    delete[] expected_histogram;
    cudaFree(d_input);
    cudaFree(d_histogram);
}

TEST_F(VectorAddSyncTest, CooperativeGroupsDotProduct) {
    float expected_dot = 0.0f;
    for (int i = 0; i < N; i++) {
        expected_dot += h_a[i] * h_b[i];
    }

    float* d_result_scalar;
    CHECK_CUDA(cudaMalloc(&d_result_scalar, sizeof(float)));
    CHECK_CUDA(cudaMemset(d_result_scalar, 0, sizeof(float)));

    dim3 block(256);
    dim3 grid(32);  // Multiple blocks for better parallelism

    vector_dot_coop_groups<<<grid, block>>>(d_a, d_b, d_result_scalar, N);
    CHECK_KERNEL_LAUNCH();

    float h_result_scalar;
    CHECK_CUDA(cudaMemcpy(&h_result_scalar, d_result_scalar, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_NEAR(h_result_scalar, expected_dot, 1e-1f);

    cudaFree(d_result_scalar);
}

TEST_F(VectorAddSyncTest, ProducerConsumerPattern) {
    const int segment_size = 256;
    const int num_segments = (N + segment_size - 1) / segment_size;

    float* d_intermediate;
    CHECK_CUDA(cudaMalloc(&d_intermediate, size));

    // Reset flags
    reset_segment_flags<<<(num_segments + 255) / 256, 256>>>(num_segments);
    CHECK_KERNEL_LAUNCH();

    // Launch producer
    vector_process_producer<<<num_segments, 256>>>(d_a, d_intermediate, N, segment_size);
    CHECK_KERNEL_LAUNCH();

    // Launch consumer
    vector_process_consumer<<<num_segments, 256>>>(d_intermediate, d_result, N, segment_size);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_result, d_result, size, cudaMemcpyDeviceToHost));

    // Verify: result should be sqrt(a^2)
    for (int i = 0; i < N; i++) {
        float expected = fabsf(h_a[i]);  // sqrt(a^2) = |a|
        EXPECT_NEAR(h_result[i], expected, 1e-4f);
    }

    cudaFree(d_intermediate);
}

TEST_F(VectorAddSyncTest, LockFreeMaximum) {
    float expected_max = *std::max_element(h_a, h_a + N);

    float* d_max;
    CHECK_CUDA(cudaMalloc(&d_max, sizeof(float)));

    float init_max = -FLT_MAX;
    CHECK_CUDA(cudaMemcpy(d_max, &init_max, sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);
    size_t shared_size = block.x * sizeof(float);

    vector_max_lockfree<<<grid, block, shared_size>>>(d_a, d_max, N);
    CHECK_KERNEL_LAUNCH();

    float h_max;
    CHECK_CUDA(cudaMemcpy(&h_max, d_max, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_NEAR(h_max, expected_max, 1e-4f);

    cudaFree(d_max);
}

TEST_F(VectorAddSyncTest, WarpVoteConvergence) {
    // Create smooth data for iterative refinement
    for (int i = 0; i < N; i++) {
        h_a[i] = sinf((float)i * 0.1f);
    }
    CHECK_CUDA(cudaMemcpy(d_a, h_a, size, cudaMemcpyHostToDevice));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    vector_refine_iterative<<<grid, block>>>(d_a, N, 1e-4f, 100);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_result, d_a, size, cudaMemcpyDeviceToHost));

    // Verify result is smooth (averaged with neighbors)
    for (int i = 1; i < N - 1; i++) {
        // Result should be some average of original values
        EXPECT_GE(h_result[i], -1.5f);
        EXPECT_LE(h_result[i], 1.5f);
    }
}

TEST_F(VectorAddSyncTest, WarpBallotPredicate) {
    float threshold = 50.0f;
    int expected_count = 0;
    for (int i = 0; i < N; i++) {
        if (h_a[i] > threshold) {
            expected_count++;
        }
    }

    int* d_count;
    CHECK_CUDA(cudaMalloc(&d_count, sizeof(int)));
    CHECK_CUDA(cudaMemset(d_count, 0, sizeof(int)));

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    vector_count_predicate<<<grid, block>>>(d_a, d_count, N, threshold);
    CHECK_KERNEL_LAUNCH();

    int h_count;
    CHECK_CUDA(cudaMemcpy(&h_count, d_count, sizeof(int), cudaMemcpyDeviceToHost));

    EXPECT_EQ(h_count, expected_count);

    cudaFree(d_count);
}

// Performance comparison
TEST_F(VectorAddSyncTest, PerformanceComparison) {
    float* d_sum;
    CHECK_CUDA(cudaMalloc(&d_sum, sizeof(float)));

    cudaEvent_t start, stop;
    CHECK_CUDA(cudaEventCreate(&start));
    CHECK_CUDA(cudaEventCreate(&stop));

    const int num_iterations = 100;
    float warp_time, coop_time;

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    // Benchmark warp shuffle reduction
    CHECK_CUDA(cudaEventRecord(start));
    for (int i = 0; i < num_iterations; i++) {
        CHECK_CUDA(cudaMemset(d_sum, 0, sizeof(float)));
        vector_sum_warp_shuffle<<<grid, block>>>(d_a, d_sum, N);
    }
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    CHECK_CUDA(cudaEventElapsedTime(&warp_time, start, stop));

    // Benchmark cooperative groups dot product
    dim3 grid_coop(32);
    CHECK_CUDA(cudaEventRecord(start));
    for (int i = 0; i < num_iterations; i++) {
        CHECK_CUDA(cudaMemset(d_sum, 0, sizeof(float)));
        vector_dot_coop_groups<<<grid_coop, block>>>(d_a, d_b, d_sum, N);
    }
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    CHECK_CUDA(cudaEventElapsedTime(&coop_time, start, stop));

    std::cout << "\nVector Operation Performance (avg over " << num_iterations << " iterations):\n";
    std::cout << "  Warp Shuffle Reduction:  " << warp_time / num_iterations << " ms\n";
    std::cout << "  Cooperative Groups Dot:  " << coop_time / num_iterations << " ms\n";

    CHECK_CUDA(cudaEventDestroy(start));
    CHECK_CUDA(cudaEventDestroy(stop));
    cudaFree(d_sum);
}
