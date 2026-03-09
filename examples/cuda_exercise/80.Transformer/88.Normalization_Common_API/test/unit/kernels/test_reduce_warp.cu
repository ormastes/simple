/**
 * @file test_reduce_warp.cu
 * @brief Unit tests for warp-level reduction primitives
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/reduce_warp.cuh"
#include <vector>
#include <numeric>
#include <algorithm>
#include <cmath>

// ---------------------------------------------------------------------------
// Test kernels
// ---------------------------------------------------------------------------

/**
 * @brief Kernel that tests warp_reduce_sum with each lane contributing its lane id
 */
__global__ void kernel_warp_reduce_sum_lane_id(float* result) {
    float val = static_cast<float>(threadIdx.x);
    float sum = transformer::warp_reduce_sum(val);
    if (threadIdx.x == 0) {
        result[0] = sum;
    }
}

/**
 * @brief Kernel that tests warp_reduce_sum with a constant value per lane
 */
__global__ void kernel_warp_reduce_sum_const(float* result, float input_val) {
    float sum = transformer::warp_reduce_sum(input_val);
    if (threadIdx.x == 0) {
        result[0] = sum;
    }
}

/**
 * @brief Kernel that tests warp_reduce_max with each lane contributing its lane id
 */
__global__ void kernel_warp_reduce_max_lane_id(float* result) {
    float val = static_cast<float>(threadIdx.x);
    float mx = transformer::warp_reduce_max(val);
    if (threadIdx.x == 0) {
        result[0] = mx;
    }
}

/**
 * @brief Kernel that tests warp_reduce_max with negative values
 */
__global__ void kernel_warp_reduce_max_negative(float* result) {
    float val = -static_cast<float>(threadIdx.x + 1);
    float mx = transformer::warp_reduce_max(val);
    if (threadIdx.x == 0) {
        result[0] = mx;
    }
}

/**
 * @brief Kernel that tests warp_reduce_min with each lane contributing its lane id
 */
__global__ void kernel_warp_reduce_min_lane_id(float* result) {
    float val = static_cast<float>(threadIdx.x);
    float mn = transformer::warp_reduce_min(val);
    if (threadIdx.x == 0) {
        result[0] = mn;
    }
}

/**
 * @brief Kernel that verifies all lanes receive the reduced result for sum
 */
__global__ void kernel_warp_reduce_sum_all_lanes(float* results) {
    float val = static_cast<float>(threadIdx.x);
    float sum = transformer::warp_reduce_sum(val);
    results[threadIdx.x] = sum;
}

/**
 * @brief Kernel that tests warp_reduce_sum with multiple warps (each warp independent)
 */
__global__ void kernel_warp_reduce_sum_multi_warp(float* results) {
    int warp_id = threadIdx.x / 32;
    float val = static_cast<float>(threadIdx.x);
    float sum = transformer::warp_reduce_sum(val);
    // Lane 0 of each warp writes the result
    if (threadIdx.x % 32 == 0) {
        results[warp_id] = sum;
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class ReduceWarpTest : public GpuTest {
protected:
    float* d_result = nullptr;

    void SetUp() override {
        GpuTest::SetUp();
        cudaMalloc(&d_result, 256 * sizeof(float));
        cudaMemset(d_result, 0, 256 * sizeof(float));
    }

    void TearDown() override {
        if (d_result) cudaFree(d_result);
        GpuTest::TearDown();
    }
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

TEST_F(ReduceWarpTest, SumLaneId) {
    // Sum of 0+1+2+...+31 = 31*32/2 = 496
    kernel_warp_reduce_sum_lane_id<<<1, 32>>>(d_result);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, 496.0f);
}

TEST_F(ReduceWarpTest, SumConstant) {
    // Each lane has value 1.0 -> sum = 32.0
    kernel_warp_reduce_sum_const<<<1, 32>>>(d_result, 1.0f);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, 32.0f);
}

TEST_F(ReduceWarpTest, SumConstantThree) {
    // Each lane has value 3.0 -> sum = 96.0
    kernel_warp_reduce_sum_const<<<1, 32>>>(d_result, 3.0f);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, 96.0f);
}

TEST_F(ReduceWarpTest, MaxLaneId) {
    // Max of 0,1,...,31 = 31
    kernel_warp_reduce_max_lane_id<<<1, 32>>>(d_result);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, 31.0f);
}

TEST_F(ReduceWarpTest, MaxNegative) {
    // Values: -1,-2,...,-32 -> max = -1
    kernel_warp_reduce_max_negative<<<1, 32>>>(d_result);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, -1.0f);
}

TEST_F(ReduceWarpTest, MinLaneId) {
    // Min of 0,1,...,31 = 0
    kernel_warp_reduce_min_lane_id<<<1, 32>>>(d_result);
    cudaDeviceSynchronize();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_result, 0.0f);
}

TEST_F(ReduceWarpTest, SumAllLanesReceiveResult) {
    // Verify that all 32 lanes get the same reduced sum
    kernel_warp_reduce_sum_all_lanes<<<1, 32>>>(d_result);
    cudaDeviceSynchronize();

    float h_results[32];
    cudaMemcpy(h_results, d_result, 32 * sizeof(float), cudaMemcpyDeviceToHost);

    float expected = 496.0f; // sum of 0..31
    for (int i = 0; i < 32; i++) {
        EXPECT_FLOAT_EQ(h_results[i], expected) << "Lane " << i << " mismatch";
    }
}

TEST_F(ReduceWarpTest, SumMultipleWarps) {
    // Launch 128 threads = 4 warps
    // Warp 0: threads 0-31, sum = 0+1+...+31 = 496
    // Warp 1: threads 32-63, sum = 32+33+...+63 = (32+63)*32/2 = 1520
    // Warp 2: threads 64-95, sum = 64+65+...+95 = (64+95)*32/2 = 2544
    // Warp 3: threads 96-127, sum = 96+97+...+127 = (96+127)*32/2 = 3568
    kernel_warp_reduce_sum_multi_warp<<<1, 128>>>(d_result);
    cudaDeviceSynchronize();

    float h_results[4];
    cudaMemcpy(h_results, d_result, 4 * sizeof(float), cudaMemcpyDeviceToHost);

    EXPECT_FLOAT_EQ(h_results[0], 496.0f);
    EXPECT_FLOAT_EQ(h_results[1], 1520.0f);
    EXPECT_FLOAT_EQ(h_results[2], 2544.0f);
    EXPECT_FLOAT_EQ(h_results[3], 3568.0f);
}
