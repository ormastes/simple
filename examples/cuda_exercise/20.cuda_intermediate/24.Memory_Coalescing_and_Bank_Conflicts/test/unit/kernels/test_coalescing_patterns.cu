/**
 * Unit tests for memory coalescing patterns
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"

// ============================================================================
// Test Kernels
// ============================================================================

__global__ void coalesced_copy(const float* __restrict__ input,
                                float* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        output[tid] = input[tid];
    }
}

__global__ void strided_copy(const float* __restrict__ input,
                              float* __restrict__ output, int n, int stride) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int idx = tid * stride;
    if (idx < n) {
        output[tid] = input[idx];
    }
}

__global__ void vectorized_copy(const float4* __restrict__ input,
                                 float4* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        output[tid] = input[tid];
    }
}

// Test fixture
class CoalescingPatternsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

// ============================================================================
// Coalescing Tests
// ============================================================================

TEST_F(CoalescingPatternsTest, CoalescedAccess) {
    const int N = 1024 * 256;
    float *h_input, *h_output;
    float *d_input, *d_output;

    // Allocate host memory
    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, N * sizeof(float)));

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }

    // Allocate device memory
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, N * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    // Launch kernel
    int blocks = (N + 255) / 256;
    coalesced_copy<<<blocks, 256>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy result back
    CHECK_CUDA(cudaMemcpy(h_output, d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify correctness
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i]) << "Mismatch at index " << i;
    }

    // Cleanup
    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(CoalescingPatternsTest, StridedAccess) {
    const int N = 1024 * 256;
    const int STRIDE = 2;
    float *h_input, *h_output;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, (N / STRIDE) * sizeof(float)));

    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }

    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, (N / STRIDE) * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    int blocks = (N / STRIDE + 255) / 256;
    strided_copy<<<blocks, 256>>>(d_input, d_output, N, STRIDE);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, (N / STRIDE) * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify: output[i] should equal input[i * STRIDE]
    for (int i = 0; i < N / STRIDE; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i * STRIDE]) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(CoalescingPatternsTest, VectorizedAccess) {
    const int N = 1024 * 256;  // Must be divisible by 4
    float *h_input, *h_output;
    float *d_input, *d_output;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, N * sizeof(float)));

    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }

    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, N * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    int blocks = (N / 4 + 255) / 256;
    vectorized_copy<<<blocks, 256>>>(
        reinterpret_cast<float4*>(d_input),
        reinterpret_cast<float4*>(d_output),
        N / 4
    );
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_output, d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i]) << "Mismatch at index " << i;
    }

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}
