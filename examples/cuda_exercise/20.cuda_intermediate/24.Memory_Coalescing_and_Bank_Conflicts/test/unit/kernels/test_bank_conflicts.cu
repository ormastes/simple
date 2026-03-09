/**
 * Unit tests for bank conflict patterns
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"

#define TILE_SIZE 32

// ============================================================================
// Test Kernels
// ============================================================================

__global__ void matrix_transpose_no_padding(const float* __restrict__ input,
                                             float* __restrict__ output,
                                             int width, int height) {
    __shared__ float tile[TILE_SIZE][TILE_SIZE];

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    if (x < width && y < height) {
        tile[threadIdx.y][threadIdx.x] = input[y * width + x];
    }
    __syncthreads();

    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;

    if (x < height && y < width) {
        output[y * height + x] = tile[threadIdx.x][threadIdx.y];
    }
}

__global__ void matrix_transpose_with_padding(const float* __restrict__ input,
                                               float* __restrict__ output,
                                               int width, int height) {
    __shared__ float tile[TILE_SIZE][TILE_SIZE + 1];  // Padding to avoid conflicts

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    if (x < width && y < height) {
        tile[threadIdx.y][threadIdx.x] = input[y * width + x];
    }
    __syncthreads();

    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;

    if (x < height && y < width) {
        output[y * height + x] = tile[threadIdx.x][threadIdx.y];
    }
}

// Test fixture
class BankConflictsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

// ============================================================================
// Bank Conflict Tests
// ============================================================================

TEST_F(BankConflictsTest, TransposeNoPadding) {
    const int SIZE = 256;
    float *h_input, *h_output, *h_expected;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_expected, SIZE * SIZE * sizeof(float)));

    // Initialize with pattern
    for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < SIZE; j++) {
            h_input[i * SIZE + j] = i * SIZE + j;
            h_expected[j * SIZE + i] = i * SIZE + j;  // Transposed
        }
    }

    CHECK_CUDA(cudaMalloc(&d_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, SIZE * SIZE * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((SIZE + TILE_SIZE - 1) / TILE_SIZE, (SIZE + TILE_SIZE - 1) / TILE_SIZE);

    matrix_transpose_no_padding<<<grid, block>>>(d_input, d_output, SIZE, SIZE);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, SIZE * SIZE * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify transpose is correct
    for (int i = 0; i < SIZE * SIZE; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_expected[i]) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFreeHost(h_expected);
    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(BankConflictsTest, TransposeWithPadding) {
    const int SIZE = 256;
    float *h_input, *h_output, *h_expected;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_expected, SIZE * SIZE * sizeof(float)));

    for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < SIZE; j++) {
            h_input[i * SIZE + j] = i * SIZE + j;
            h_expected[j * SIZE + i] = i * SIZE + j;
        }
    }

    CHECK_CUDA(cudaMalloc(&d_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, SIZE * SIZE * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((SIZE + TILE_SIZE - 1) / TILE_SIZE, (SIZE + TILE_SIZE - 1) / TILE_SIZE);

    matrix_transpose_with_padding<<<grid, block>>>(d_input, d_output, SIZE, SIZE);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, SIZE * SIZE * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < SIZE * SIZE; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_expected[i]) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFreeHost(h_expected);
    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(BankConflictsTest, PaddingEliminatesConflicts) {
    // This test verifies both implementations produce identical results
    // The padded version should be faster (tested via benchmarking)
    const int SIZE = 128;
    float *h_input;
    float *d_input, *d_output_no_pad, *d_output_with_pad;
    float *h_output_no_pad, *h_output_with_pad;

    CHECK_CUDA(cudaMallocHost(&h_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output_no_pad, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output_with_pad, SIZE * SIZE * sizeof(float)));

    for (int i = 0; i < SIZE * SIZE; i++) {
        h_input[i] = static_cast<float>(i);
    }

    CHECK_CUDA(cudaMalloc(&d_input, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output_no_pad, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output_with_pad, SIZE * SIZE * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, SIZE * SIZE * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((SIZE + TILE_SIZE - 1) / TILE_SIZE, (SIZE + TILE_SIZE - 1) / TILE_SIZE);

    // Run both versions
    matrix_transpose_no_padding<<<grid, block>>>(d_input, d_output_no_pad, SIZE, SIZE);
    matrix_transpose_with_padding<<<grid, block>>>(d_input, d_output_with_pad, SIZE, SIZE);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output_no_pad, d_output_no_pad, SIZE * SIZE * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_output_with_pad, d_output_with_pad, SIZE * SIZE * sizeof(float), cudaMemcpyDeviceToHost));

    // Both should produce identical results
    for (int i = 0; i < SIZE * SIZE; i++) {
        EXPECT_FLOAT_EQ(h_output_no_pad[i], h_output_with_pad[i])
            << "Results differ at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output_no_pad);
    cudaFreeHost(h_output_with_pad);
    cudaFree(d_input);
    cudaFree(d_output_no_pad);
    cudaFree(d_output_with_pad);
}
