/**
 * @file test_reduce_block.cu
 * @brief Unit tests for block-level reduction primitives
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/reduce_block.cuh"
#include <vector>
#include <numeric>
#include <algorithm>
#include <cmath>

// ---------------------------------------------------------------------------
// Test kernels
// ---------------------------------------------------------------------------

/**
 * @brief Kernel that tests block_reduce_sum with each thread contributing its thread id
 */
__global__ void kernel_block_reduce_sum_tid(float* result) {
    extern __shared__ float smem[];
    float val = static_cast<float>(threadIdx.x);
    float sum = transformer::block_reduce_sum(val, smem);
    if (threadIdx.x == 0) {
        result[0] = sum;
    }
}

/**
 * @brief Kernel that tests block_reduce_sum with constant value
 */
__global__ void kernel_block_reduce_sum_const(float* result, float input_val) {
    extern __shared__ float smem[];
    float sum = transformer::block_reduce_sum(input_val, smem);
    if (threadIdx.x == 0) {
        result[0] = sum;
    }
}

/**
 * @brief Kernel that tests block_reduce_max with each thread contributing its thread id
 */
__global__ void kernel_block_reduce_max_tid(float* result) {
    extern __shared__ float smem[];
    float val = static_cast<float>(threadIdx.x);
    float mx = transformer::block_reduce_max(val, smem);
    if (threadIdx.x == 0) {
        result[0] = mx;
    }
}

/**
 * @brief Kernel that tests block_reduce_max with negative values
 */
__global__ void kernel_block_reduce_max_neg(float* result) {
    extern __shared__ float smem[];
    float val = -static_cast<float>(threadIdx.x + 1);
    float mx = transformer::block_reduce_max(val, smem);
    if (threadIdx.x == 0) {
        result[0] = mx;
    }
}

/**
 * @brief Kernel that tests block_reduce_sum with data from global memory
 */
__global__ void kernel_block_reduce_sum_array(const float* input, float* result, int n) {
    extern __shared__ float smem[];
    float val = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        val += input[i];
    }
    float sum = transformer::block_reduce_sum(val, smem);
    if (threadIdx.x == 0) {
        result[0] = sum;
    }
}

/**
 * @brief Kernel verifying all threads receive broadcast result
 */
__global__ void kernel_block_reduce_sum_broadcast(float* results) {
    extern __shared__ float smem[];
    float val = static_cast<float>(threadIdx.x);
    float sum = transformer::block_reduce_sum(val, smem);
    results[threadIdx.x] = sum;
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class ReduceBlockTest : public GpuTest {
protected:
    float* d_result = nullptr;
    float* d_input = nullptr;
    float* d_broadcast = nullptr;

    void SetUp() override {
        GpuTest::SetUp();
        cudaMalloc(&d_result, sizeof(float));
        cudaMemset(d_result, 0, sizeof(float));
    }

    void TearDown() override {
        if (d_result) cudaFree(d_result);
        if (d_input) cudaFree(d_input);
        if (d_broadcast) cudaFree(d_broadcast);
        GpuTest::TearDown();
    }

    float getResult() {
        float h_result;
        cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
        return h_result;
    }

    /// @brief Compute shared memory size needed for N threads
    size_t smemSize(int num_threads) {
        return ((num_threads + 31) / 32) * sizeof(float);
    }
};

// ---------------------------------------------------------------------------
// Tests with 128 threads (4 warps)
// ---------------------------------------------------------------------------

TEST_F(ReduceBlockTest, Sum128Threads_ThreadId) {
    // Sum of 0+1+...+127 = 127*128/2 = 8128
    int N = 128;
    kernel_block_reduce_sum_tid<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 8128.0f);
}

TEST_F(ReduceBlockTest, Sum128Threads_Const) {
    // 128 threads * 2.0 = 256.0
    int N = 128;
    kernel_block_reduce_sum_const<<<1, N, smemSize(N)>>>(d_result, 2.0f);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 256.0f);
}

TEST_F(ReduceBlockTest, Max128Threads_ThreadId) {
    // Max of 0,1,...,127 = 127
    int N = 128;
    kernel_block_reduce_max_tid<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 127.0f);
}

// ---------------------------------------------------------------------------
// Tests with 256 threads (8 warps)
// ---------------------------------------------------------------------------

TEST_F(ReduceBlockTest, Sum256Threads_ThreadId) {
    // Sum of 0+1+...+255 = 255*256/2 = 32640
    int N = 256;
    kernel_block_reduce_sum_tid<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 32640.0f);
}

TEST_F(ReduceBlockTest, Max256Threads_ThreadId) {
    // Max of 0,...,255 = 255
    int N = 256;
    kernel_block_reduce_max_tid<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 255.0f);
}

// ---------------------------------------------------------------------------
// Tests with 512 threads (16 warps)
// ---------------------------------------------------------------------------

TEST_F(ReduceBlockTest, Sum512Threads_ThreadId) {
    // Sum of 0+1+...+511 = 511*512/2 = 130816
    int N = 512;
    kernel_block_reduce_sum_tid<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), 130816.0f);
}

TEST_F(ReduceBlockTest, Max512Threads_Negative) {
    // Values: -1,-2,...,-512 -> max = -1
    int N = 512;
    kernel_block_reduce_max_neg<<<1, N, smemSize(N)>>>(d_result);
    cudaDeviceSynchronize();
    EXPECT_FLOAT_EQ(getResult(), -1.0f);
}

// ---------------------------------------------------------------------------
// Tests with global memory input
// ---------------------------------------------------------------------------

TEST_F(ReduceBlockTest, SumArray_1024Elements_256Threads) {
    // Create array [1, 2, 3, ..., 1024], sum = 1024*1025/2 = 524800
    int n = 1024;
    int blockSize = 256;
    std::vector<float> h_input(n);
    for (int i = 0; i < n; i++) {
        h_input[i] = static_cast<float>(i + 1);
    }

    cudaMalloc(&d_input, n * sizeof(float));
    cudaMemcpy(d_input, h_input.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    kernel_block_reduce_sum_array<<<1, blockSize, smemSize(blockSize)>>>(d_input, d_result, n);
    cudaDeviceSynchronize();

    float expected = static_cast<float>(n) * static_cast<float>(n + 1) / 2.0f;
    EXPECT_NEAR(getResult(), expected, 1.0f);
}

// ---------------------------------------------------------------------------
// Test broadcast: all threads should receive the same result
// ---------------------------------------------------------------------------

TEST_F(ReduceBlockTest, SumBroadcast_256Threads) {
    int N = 256;
    cudaMalloc(&d_broadcast, N * sizeof(float));
    cudaMemset(d_broadcast, 0, N * sizeof(float));

    kernel_block_reduce_sum_broadcast<<<1, N, smemSize(N)>>>(d_broadcast);
    cudaDeviceSynchronize();

    std::vector<float> h_results(N);
    cudaMemcpy(h_results.data(), d_broadcast, N * sizeof(float), cudaMemcpyDeviceToHost);

    float expected = 255.0f * 256.0f / 2.0f; // 32640
    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_results[i], expected) << "Thread " << i << " mismatch";
    }
}
