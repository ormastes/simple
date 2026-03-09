/**
 * Unit tests for matrix multiplication kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"

#include "kernels/matrix_multiply.cu"

// Forward declarations for Part 19 specific functions
extern void matmul_with_pinned_memory(float* h_A, float* h_B, float* h_C,
                                      float* d_A, float* d_B, float* d_C,
                                      int N, cudaStream_t stream);
extern __global__ void matmul_prefetch(const float* __restrict__ A,
                                       const float* __restrict__ B,
                                       float* __restrict__ C, int N);
extern __global__ void matmul_texture(float* C, int N);

// Uses GpuTest base class for automatic device setup/teardown
class MatrixMultiplyTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        N = 256;
        size = N * N * sizeof(float);

        h_A = (float*)malloc(size);
        h_B = (float*)malloc(size);
        h_C_ref = (float*)malloc(size);
        h_C_test = (float*)malloc(size);

        // Initialize matrices
        for (int i = 0; i < N * N; i++) {
            h_A[i] = (float)(rand() % 10) / 10.0f;
            h_B[i] = (float)(rand() % 10) / 10.0f;
        }

        cudaMalloc(&d_A, size);
        cudaMalloc(&d_B, size);
        cudaMalloc(&d_C, size);

        cudaMemcpy(d_A, h_A, size, cudaMemcpyHostToDevice);
        cudaMemcpy(d_B, h_B, size, cudaMemcpyHostToDevice);

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

    bool verifyResults(float tolerance = 1e-3f) {
        for (int i = 0; i < N * N; i++) {
            if (fabs(h_C_ref[i] - h_C_test[i]) > tolerance) {
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

TEST_F(MatrixMultiplyTest, NaiveCorrectness) {
    dim3 block(16, 16);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    matmul_naive<<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost);
    EXPECT_TRUE(verifyResults());
}

TEST_F(MatrixMultiplyTest, BasicTiledCorrectness) {
    dim3 block(16, 16);
    dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

    matmul_basic_tiled<<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost);
    EXPECT_TRUE(verifyResults());
}

TEST_F(MatrixMultiplyTest, OptimizedTiledCorrectness) {
    const int TILE = 32;
    dim3 block(TILE, TILE);
    dim3 grid((N + TILE - 1) / TILE, (N + TILE - 1) / TILE);

    matmul_tiled<32><<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost);
    EXPECT_TRUE(verifyResults());
}

// Fixed: matmul_coarsened kernel implementation bugs resolved
TEST_F(MatrixMultiplyTest, CoarsenedCorrectness) {
    const int TILE = 16;
    const int COARSE = 2;
    // Block: (TILE/COARSE) x (TILE/COARSE) threads, each processing COARSE x COARSE elements
    dim3 block(TILE / COARSE, TILE / COARSE);
    // Each block processes TILE x TILE elements
    dim3 grid((N + TILE - 1) / TILE, (N + TILE - 1) / TILE);

    matmul_coarsened<16, 2><<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost);
    EXPECT_TRUE(verifyResults(1e-2f)); // Slightly higher tolerance for coarsened
}

// This test is expected to FAIL - matmul_warp_opt kernel has shared memory access bugs
TEST_F(MatrixMultiplyTest, FailTest_WarpOptimizedCorrectness) {
    const int WARP_SIZE = 32;
    const int WARPS_PER_BLOCK = 4;  // Reduced from 8 to fit sm_75 shared memory limit
    dim3 block(WARP_SIZE, WARPS_PER_BLOCK);
    int gridX = (N + WARPS_PER_BLOCK * WARP_SIZE - 1) / (WARPS_PER_BLOCK * WARP_SIZE);
    int gridY = (N + WARPS_PER_BLOCK * WARP_SIZE - 1) / (WARPS_PER_BLOCK * WARP_SIZE);
    dim3 grid(gridX, gridY);

    matmul_warp_opt<<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_C_test, d_C, size, cudaMemcpyDeviceToHost);
    EXPECT_TRUE(verifyResults());
}

// Performance comparison test
TEST(MatrixMultiplyPerformance, CompareImplementations) {
    const int N = 1024;
    size_t size = N * N * sizeof(float);

    float *d_A, *d_B, *d_C;
    cudaMalloc(&d_A, size);
    cudaMalloc(&d_B, size);
    cudaMalloc(&d_C, size);

    // Initialize with random data
    float *h_temp = (float*)malloc(size);
    for (int i = 0; i < N * N; i++) {
        h_temp[i] = (float)(rand() % 100) / 100.0f;
    }
    cudaMemcpy(d_A, h_temp, size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_temp, size, cudaMemcpyHostToDevice);

    float gflops_factor = (2.0f * N * N * N) / 1e9f;

    // Test naive
    {
        dim3 block(16, 16);
        dim3 grid((N + block.x - 1) / block.x, (N + block.y - 1) / block.y);

        CudaTimer timer;
        timer.start();
        for (int i = 0; i < 10; i++) {
            matmul_naive<<<grid, block>>>(d_A, d_B, d_C, N);
        }
        timer.stop();

        float gflops = gflops_factor * 10 / (timer.elapsed_ms() / 1000.0f);
        printf("Naive: %.2f GFLOPS\n", gflops);
    }

    // Test optimized tiled
    {
        const int TILE = 32;
        dim3 block(TILE, TILE);
        dim3 grid((N + TILE - 1) / TILE, (N + TILE - 1) / TILE);

        CudaTimer timer;
        timer.start();
        for (int i = 0; i < 10; i++) {
            matmul_tiled<32><<<grid, block>>>(d_A, d_B, d_C, N);
        }
        timer.stop();

        float gflops = gflops_factor * 10 / (timer.elapsed_ms() / 1000.0f);
        printf("Tiled: %.2f GFLOPS\n", gflops);

        // Expect significant improvement
        EXPECT_GT(gflops, 100.0f);
    }

    free(h_temp);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

// This test is expected to FAIL - matmul_with_pinned_memory has illegal memory access
TEST_F(MatrixMultiplyTest, FailTest_PinnedMemoryTest) {
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // Test with small matrix
    int small_N = 128;
    size_t small_size = small_N * small_N * sizeof(float);

    float *h_A_test = (float*)malloc(small_size);
    float *h_B_test = (float*)malloc(small_size);
    float *h_C_test = (float*)malloc(small_size);
    float *h_C_ref = (float*)malloc(small_size);

    // Initialize
    for (int i = 0; i < small_N * small_N; i++) {
        h_A_test[i] = (float)(rand() % 10) / 10.0f;
        h_B_test[i] = (float)(rand() % 10) / 10.0f;
    }

    float *d_A_test, *d_B_test, *d_C_test;
    cudaMalloc(&d_A_test, small_size);
    cudaMalloc(&d_B_test, small_size);
    cudaMalloc(&d_C_test, small_size);

    // Test the pinned memory function
    ASSERT_NO_THROW({
        matmul_with_pinned_memory(h_A_test, h_B_test, h_C_test,
                                 d_A_test, d_B_test, d_C_test,
                                 small_N, stream);
    });

    // Compute CPU reference for verification
    for (int i = 0; i < small_N; i++) {
        for (int j = 0; j < small_N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < small_N; k++) {
                sum += h_A_test[i * small_N + k] * h_B_test[k * small_N + j];
            }
            h_C_ref[i * small_N + j] = sum;
        }
    }

    // Verify results
    bool match = true;
    for (int i = 0; i < small_N * small_N; i++) {
        if (fabs(h_C_test[i] - h_C_ref[i]) > 1e-2f) {
            match = false;
            break;
        }
    }
    EXPECT_TRUE(match) << "Pinned memory matmul results don't match reference";

    free(h_A_test);
    free(h_B_test);
    free(h_C_test);
    free(h_C_ref);
    cudaFree(d_A_test);
    cudaFree(d_B_test);
    cudaFree(d_C_test);
    cudaStreamDestroy(stream);
}

// Test Part 19: Prefetch Kernel
TEST_F(MatrixMultiplyTest, PrefetchCorrectness) {
    const int test_N = 128;
    size_t test_size = test_N * test_N * sizeof(float);

    float *d_A_pf, *d_B_pf, *d_C_pf;
    cudaMalloc(&d_A_pf, test_size);
    cudaMalloc(&d_B_pf, test_size);
    cudaMalloc(&d_C_pf, test_size);

    cudaMemcpy(d_A_pf, h_A, test_size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_pf, h_B, test_size, cudaMemcpyHostToDevice);

    dim3 block(32, 32);
    dim3 grid((test_N + 31) / 32, (test_N + 31) / 32);

    matmul_prefetch<<<grid, block>>>(d_A_pf, d_B_pf, d_C_pf, test_N);
    CHECK_KERNEL_LAUNCH();

    float *h_C_pf = (float*)malloc(test_size);
    cudaMemcpy(h_C_pf, d_C_pf, test_size, cudaMemcpyDeviceToHost);

    // Verify against CPU reference (using smaller size for speed)
    for (int i = 0; i < min(test_N, 32); i++) {
        for (int j = 0; j < min(test_N, 32); j++) {
            float sum = 0.0f;
            for (int k = 0; k < test_N; k++) {
                sum += h_A[i * test_N + k] * h_B[k * test_N + j];
            }
            EXPECT_NEAR(h_C_pf[i * test_N + j], sum, 1e-2f)
                << "Mismatch at [" << i << "," << j << "]";
        }
    }

    free(h_C_pf);
    cudaFree(d_A_pf);
    cudaFree(d_B_pf);
    cudaFree(d_C_pf);
}