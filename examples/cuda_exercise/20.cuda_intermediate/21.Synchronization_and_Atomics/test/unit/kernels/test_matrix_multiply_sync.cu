/**
 * Unit tests for synchronization-optimized matrix multiplication kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"  // From GTestBasicLib, via CMake
#include "kernels/matrix_multiply_sync.cu"

// Test fixture using GpuTest base class
class MatrixMultiplySyncTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        N = 128;  // Smaller for faster tests
        size = N * N * sizeof(float);

        h_A = (float*)malloc(size);
        h_B = (float*)malloc(size);
        h_C_ref = (float*)malloc(size);
        h_C_test = (float*)malloc(size);

        // Initialize with simple pattern
        for (int i = 0; i < N * N; i++) {
            h_A[i] = (float)(i % 10) * 0.1f;
            h_B[i] = (float)((i / 10) % 10) * 0.1f;
        }

        CHECK_CUDA(cudaMalloc(&d_A, size));
        CHECK_CUDA(cudaMalloc(&d_B, size));
        CHECK_CUDA(cudaMalloc(&d_C, size));

        CHECK_CUDA(cudaMemcpy(d_A, h_A, size, cudaMemcpyHostToDevice));
        CHECK_CUDA(cudaMemcpy(d_B, h_B, size, cudaMemcpyHostToDevice));

        // Compute reference on CPU
        computeReference();
    }

    void TearDown() override {
        free(h_A);
        free(h_B);
        free(h_C_ref);
        free(h_C_test);
        cudaFree(d_A);
        cudaFree(d_B);
        cudaFree(d_C);

        GpuTest::TearDown();
    }

    void computeReference() {
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                float sum = 0.0f;
                for (int k = 0; k < N; k++) {
                    sum += h_A[i * N + k] * h_B[k * N + j];
                }
                h_C_ref[i * N + j] = sum;
            }
        }
    }

    bool verifyResults(float tolerance = 1e-2f) {
        for (int i = 0; i < N * N; i++) {
            if (fabsf(h_C_ref[i] - h_C_test[i]) > tolerance) {
                printf("Mismatch at index %d: expected %f, got %f\n",
                       i, h_C_ref[i], h_C_test[i]);
                return false;
            }
        }
        return true;
    }

    int N;
    size_t size;
    float *h_A, *h_B, *h_C_ref, *h_C_test;
    float *d_A, *d_B, *d_C;
};

TEST_F(MatrixMultiplySyncTest, WarpReductionCorrectness) {
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    CHECK_CUDA(cudaMemset(d_C, 0, size));
    matmul_warp_reduction<<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost));
    EXPECT_TRUE(verifyResults());
}

TEST_F(MatrixMultiplySyncTest, CooperativeGroupsCorrectness) {
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    CHECK_CUDA(cudaMemset(d_C, 0, size));
    matmul_cooperative_groups<<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost));
    EXPECT_TRUE(verifyResults());
}

TEST_F(MatrixMultiplySyncTest, AtomicAccumulateCorrectness) {
    // Use TILE_SIZE=32 to match kernel implementation
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    // Zero out C since we're using atomic add
    CHECK_CUDA(cudaMemset(d_C, 0, size));

    matmul_atomic_accumulate<<<grid, block>>>(d_A, d_B, d_C, N, N, N);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost));
    EXPECT_TRUE(verifyResults());
}

TEST_F(MatrixMultiplySyncTest, ProducerConsumerPattern) {
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);
    int num_tiles = grid.x * grid.y;

    float* d_intermediate;
    CHECK_CUDA(cudaMalloc(&d_intermediate, size));

    // Reset flags
    reset_tile_flags<<<(num_tiles + 255) / 256, 256>>>(num_tiles);
    CHECK_KERNEL_LAUNCH();

    // Launch producer
    matmul_producer<<<grid, block>>>(d_A, d_B, d_intermediate, N);
    CHECK_KERNEL_LAUNCH();

    // Launch consumer
    matmul_consumer<<<grid, block>>>(d_intermediate, d_C, N, num_tiles);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost));

    // Verify intermediate results (A * B element-wise)
    for (int i = 0; i < N * N; i++) {
        float expected = h_A[i] * h_B[i];
        EXPECT_NEAR(h_C_test[i], expected, 1e-4f);
    }

    cudaFree(d_intermediate);
}

TEST_F(MatrixMultiplySyncTest, IterativeRefinementConvergence) {
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    CHECK_CUDA(cudaMemset(d_C, 0, size));

    // Run iterative refinement (should converge quickly for this simple case)
    matmul_iterative_refinement<<<grid, block>>>(d_A, d_B, d_C, N, 1e-4f);
    CHECK_KERNEL_LAUNCH();

    CHECK_CUDA(cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost));
    EXPECT_TRUE(verifyResults(1e-2f));  // Looser tolerance for iterative method
}

// Performance comparison test (informational)
TEST_F(MatrixMultiplySyncTest, PerformanceComparison) {
    dim3 block(32, 32);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    cudaEvent_t start, stop;
    CHECK_CUDA(cudaEventCreate(&start));
    CHECK_CUDA(cudaEventCreate(&stop));

    const int num_iterations = 10;
    float times[3];

    // Benchmark warp reduction
    CHECK_CUDA(cudaEventRecord(start));
    for (int i = 0; i < num_iterations; i++) {
        matmul_warp_reduction<<<grid, block>>>(d_A, d_B, d_C, N);
    }
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    CHECK_CUDA(cudaEventElapsedTime(&times[0], start, stop));

    // Benchmark cooperative groups
    CHECK_CUDA(cudaEventRecord(start));
    for (int i = 0; i < num_iterations; i++) {
        matmul_cooperative_groups<<<grid, block>>>(d_A, d_B, d_C, N);
    }
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    CHECK_CUDA(cudaEventElapsedTime(&times[1], start, stop));

    // Benchmark atomic accumulate
    CHECK_CUDA(cudaEventRecord(start));
    for (int i = 0; i < num_iterations; i++) {
        CHECK_CUDA(cudaMemset(d_C, 0, size));
        matmul_atomic_accumulate<<<grid, block>>>(d_A, d_B, d_C, N, N, N);
    }
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    CHECK_CUDA(cudaEventElapsedTime(&times[2], start, stop));

    std::cout << "\nPerformance (avg over " << num_iterations << " iterations):\n";
    std::cout << "  Warp Reduction:     " << times[0] / num_iterations << " ms\n";
    std::cout << "  Cooperative Groups: " << times[1] / num_iterations << " ms\n";
    std::cout << "  Atomic Accumulate:  " << times[2] / num_iterations << " ms\n";

    CHECK_CUDA(cudaEventDestroy(start));
    CHECK_CUDA(cudaEventDestroy(stop));
}
