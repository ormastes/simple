/**
 * Unit tests for shared memory kernels (from module 22)
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"  // From GTestBasicLib
#include "cuda_utils.h"  // For CHECK_CUDA and CHECK_KERNEL_LAUNCH macros

// Forward declarations of kernel functions (defined in library)
// Note: Kernels are linked from 23_Shared_Memory_lib, not included directly

// Matrix multiplication kernels
__global__ void matmul_producer_stage(const float* A, const float* B, float* C, float* partial, int M, int N, int K, float alpha);
template<int TILE_SIZE>
__global__ void matmul_consumer_stage(const float* A, const float* B, float* C, int M, int N, int K);
template<int TILE_SIZE>
__global__ void matmul_prefetch_double_buffer(const float* A, const float* B, float* C, int M, int N, int K);

// Vector operation kernels
__global__ void vector_add_chunk(const float* a, const float* b, float* c, int n, int chunk_id);
__global__ void reduction_stage1(const float* input, float* partial, int n, int blocks_per_stage);
__global__ void reduction_stage2(const float* partial, float* output, int n);
__device__ float warp_reduce(float val);
__global__ void histogram_chunk(const int* data, int* histogram, int n, int num_bins, int chunk_id);
__global__ void vector_process_buffered(float* data, int n, float scale, int buffer_size);
__global__ void vector_producer(float* data, int n, int chunk_size, float value);
__global__ void vector_consumer(const float* data, float* result, int n, int chunk_size);
__global__ void dot_product_chunk(const float* a, const float* b, float* partial, int n, int chunk_size, int chunk_id);

struct WorkItem {
    float* data;
    int size;
    int type;  // 0=add, 1=multiply, 2=scale
    float param;
};

__global__ void persistent_vector_processor(WorkItem* work_queue, volatile int* queue_size, int max_items);
__global__ void compute_statistics(const float* data, float* mean, float* variance, int n);
__global__ void vector_transform_managed(float* data, int n, float scale);
__global__ void vector_scale_graph(float* data, int n, float scale);
__global__ void vector_add_graph(const float* a, const float* b, float* c, int n);
__global__ void vector_add_peer(const float* a, const float* b, float* c, int n);

// Test fixture
class SharedMemoryKernelsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

// =============================================================================
// Matrix Multiplication Tests
// =============================================================================

TEST_F(SharedMemoryKernelsTest, MatMulTiledWithPadding) {
    const int M = 128, N = 128, K = 128;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C, *h_C_ref;
    float *d_A, *d_B, *d_C;

    size_t size_A = M * K * sizeof(float);
    size_t size_B = K * N * sizeof(float);
    size_t size_C = M * N * sizeof(float);

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_A, size_A));
    CHECK_CUDA(cudaMallocHost(&h_B, size_B));
    CHECK_CUDA(cudaMallocHost(&h_C, size_C));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, size_C));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (i % 10) * 0.1f;
    for (int i = 0; i < K * N; i++) h_B[i] = (i % 10) * 0.1f;

    // Compute reference on CPU
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += h_A[i * K + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    // Allocate device memory
    CHECK_CUDA(cudaMalloc(&d_A, size_A));
    CHECK_CUDA(cudaMalloc(&d_B, size_B));
    CHECK_CUDA(cudaMalloc(&d_C, size_C));
    CHECK_CUDA(cudaMemcpy(d_A, h_A, size_A, cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, size_B, cudaMemcpyHostToDevice));

    // Launch kernel with bank conflict padding
    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);
    matmul_consumer_stage<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_C, d_C, size_C, cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C);
    cudaFreeHost(h_C_ref);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

TEST_F(SharedMemoryKernelsTest, MatMulPrefetchDoubleBuffer) {
    const int M = 64, N = 64, K = 64;
    const int TILE_SIZE = 16;

    float *h_A, *h_B, *h_C, *h_C_ref;
    float *d_A, *d_B, *d_C;

    size_t size_A = M * K * sizeof(float);
    size_t size_B = K * N * sizeof(float);
    size_t size_C = M * N * sizeof(float);

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_A, size_A));
    CHECK_CUDA(cudaMallocHost(&h_B, size_B));
    CHECK_CUDA(cudaMallocHost(&h_C, size_C));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, size_C));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (i % 7) * 0.1f;
    for (int i = 0; i < K * N; i++) h_B[i] = (i % 7) * 0.1f;

    // Compute reference
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += h_A[i * K + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    // Allocate device memory
    CHECK_CUDA(cudaMalloc(&d_A, size_A));
    CHECK_CUDA(cudaMalloc(&d_B, size_B));
    CHECK_CUDA(cudaMalloc(&d_C, size_C));
    CHECK_CUDA(cudaMemcpy(d_A, h_A, size_A, cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, size_B, cudaMemcpyHostToDevice));

    // Launch prefetch double buffer kernel
    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);
    matmul_prefetch_double_buffer<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_C, d_C, size_C, cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C);
    cudaFreeHost(h_C_ref);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

// =============================================================================
// Vector Operations Tests
// =============================================================================

TEST_F(SharedMemoryKernelsTest, ReductionWithSharedMemory) {
    const int N = 1024 * 256;
    const int BLOCK_SIZE = 256;

    float *h_input, *h_partial;
    float *d_input, *d_partial;

    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_partial, num_blocks * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_partial, num_blocks * sizeof(float)));

    // Initialize with ones
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch reduction kernel
    int shared_mem = BLOCK_SIZE * sizeof(float);
    reduction_stage1<<<num_blocks, BLOCK_SIZE, shared_mem>>>(
        d_input, d_partial, N, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy partial results
    CHECK_CUDA(cudaMemcpy(h_partial, d_partial, num_blocks * sizeof(float), cudaMemcpyDeviceToHost));

    // Final sum on CPU
    float result = 0.0f;
    for (int i = 0; i < num_blocks; i++) {
        result += h_partial[i];
    }

    // Verify (should be N since all elements are 1.0f)
    EXPECT_NEAR(result, static_cast<float>(N), N * 1e-5f);

    // Cleanup
    cudaFreeHost(h_input);
    cudaFreeHost(h_partial);
    cudaFree(d_input);
    cudaFree(d_partial);
}

TEST_F(SharedMemoryKernelsTest, HistogramWithSharedMemory) {
    const int N = 1024;
    const int NUM_BINS = 16;
    const int BLOCK_SIZE = 256;

    int *h_input, *h_histogram, *h_expected;
    int *d_input, *d_histogram;

    // Allocate memory
    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_histogram, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_expected, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_histogram, NUM_BINS * sizeof(int)));

    // Initialize input with known pattern
    for (int i = 0; i < NUM_BINS; i++) h_expected[i] = 0;
    for (int i = 0; i < N; i++) {
        h_input[i] = i % NUM_BINS;
        h_expected[i % NUM_BINS]++;
    }

    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_histogram, 0, NUM_BINS * sizeof(int)));

    // Launch histogram kernel
    int shared_mem = NUM_BINS * sizeof(int);
    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
    histogram_chunk<<<num_blocks, BLOCK_SIZE, shared_mem>>>(
        d_input, d_histogram, NUM_BINS, N, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result
    CHECK_CUDA(cudaMemcpy(h_histogram, d_histogram, NUM_BINS * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify
    for (int i = 0; i < NUM_BINS; i++) {
        EXPECT_EQ(h_histogram[i], h_expected[i]) << "Mismatch at bin " << i;
    }

    // Cleanup
    cudaFreeHost(h_input);
    cudaFreeHost(h_histogram);
    cudaFreeHost(h_expected);
    cudaFree(d_input);
    cudaFree(d_histogram);
}
