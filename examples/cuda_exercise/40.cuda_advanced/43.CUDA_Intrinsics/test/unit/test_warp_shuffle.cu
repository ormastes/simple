// test_warp_shuffle.cu - Tests for warp shuffle intrinsics

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/warp_shuffle.cu"

class WarpShuffleTest : public GpuTest {};

TEST_F(WarpShuffleTest, BlockReduceSumWorks) {
    const int N = 1024;
    int* h_input = new int[N];
    int h_output = 0;

    // Initialize input: all ones
    for (int i = 0; i < N; i++) {
        h_input[i] = 1;
    }

    // Allocate device memory
    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(1);
    cuda_memset(d_output, 0, 1);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernel with shared memory
    int threads = 256;
    int blocks = (N + threads - 1) / threads;
    size_t shmem_size = (threads / 32) * sizeof(int);
    block_reduce_kernel<<<blocks, threads, shmem_size>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(&h_output, d_output, 1);

    // Verify: sum of N ones should be N
    EXPECT_EQ(h_output, N) << "Block reduction failed";

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
}

TEST_F(WarpShuffleTest, WarpScanProducesCorrectPrefixSum) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    int* h_output = new int[N];

    // Initialize input: all ones
    for (int i = 0; i < N; i++) {
        h_input[i] = 1;
    }

    // Allocate device memory
    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(N);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernel
    warp_scan_kernel<<<1, 32>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_output, d_output, N);

    // Verify: prefix sum of ones should be 1, 2, 3, ..., N
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], i + 1) << "Prefix sum mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(WarpShuffleTest, WarpReverseWorks) {
    const int N = 32;  // One warp
    int* h_data = new int[N];

    // Initialize input: 0, 1, 2, ..., 31
    for (int i = 0; i < N; i++) {
        h_data[i] = i;
    }

    // Allocate device memory
    int* d_data = cuda_malloc<int>(N);

    // Copy to device
    cuda_memcpy_h2d(d_data, h_data, N);

    // Launch kernel
    warp_reverse_kernel<<<1, 32>>>(d_data, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify: should be reversed (31, 30, 29, ..., 0)
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_data[i], 31 - i) << "Reverse mismatch at index " << i;
    }

    // Cleanup
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(WarpShuffleTest, ButterflyExchangeWorks) {
    const int N = 32;  // One warp
    float* h_data = new float[N];

    // Initialize input: all ones
    for (int i = 0; i < N; i++) {
        h_data[i] = 1.0f;
    }

    // Allocate device memory
    float* d_data = cuda_malloc<float>(N);

    // Copy to device
    cuda_memcpy_h2d(d_data, h_data, N);

    // Launch kernel for stage 0 (exchange with distance 1)
    butterfly_exchange_kernel<<<1, 32>>>(d_data, N, 0);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(h_data, d_data, N);

    // Verify: butterfly with all ones
    // Even indices: 1 + 1 = 2
    // Odd indices: 1 - 1 = 0
    for (int i = 0; i < N; i++) {
        if (i % 2 == 0) {
            EXPECT_FLOAT_EQ(h_data[i], 2.0f) << "Even index mismatch at " << i;
        } else {
            EXPECT_FLOAT_EQ(h_data[i], 0.0f) << "Odd index mismatch at " << i;
        }
    }

    // Cleanup
    cuda_free(d_data);
    delete[] h_data;
}

TEST_F(WarpShuffleTest, MultipleWarpsReduceCorrectly) {
    const int N = 256;  // 8 warps
    int* h_input = new int[N];
    int h_output = 0;

    // Initialize input: sequential values
    for (int i = 0; i < N; i++) {
        h_input[i] = i + 1;
    }

    // Allocate device memory
    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(1);
    cuda_memset(d_output, 0, 1);

    // Copy to device
    cuda_memcpy_h2d(d_input, h_input, N);

    // Launch kernel
    int threads = 256;
    int blocks = 1;
    size_t shmem_size = (threads / 32) * sizeof(int);
    block_reduce_kernel<<<blocks, threads, shmem_size>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cuda_memcpy_d2h(&h_output, d_output, 1);

    // Verify: sum of 1+2+...+256 = 256*257/2 = 32896
    int expected = (N * (N + 1)) / 2;
    EXPECT_EQ(h_output, expected) << "Multi-warp reduction failed";

    // Cleanup
    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
}
