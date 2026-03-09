// test_scheduling.cu - Tests for hardware scheduling and occupancy

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "host/occupancy_calculator.cpp"
#include "kernels/scheduling_kernels.cu"

class SchedulingTest : public GpuTest {};

TEST_F(SchedulingTest, OccupancyCalculatorCreation) {
    OccupancyCalculator calc(0);

    // Verify device properties were loaded
    EXPECT_GT(calc.deviceProps.multiProcessorCount, 0);
    EXPECT_GT(calc.deviceProps.maxThreadsPerMultiProcessor, 0);
    EXPECT_EQ(calc.deviceProps.warpSize, 32);
}

TEST_F(SchedulingTest, CalculateOccupancyBasic) {
    OccupancyCalculator calc(0);

    // Test with typical block size
    OccupancyResult result = calc.calculateOccupancy(256, 0, 0);

    EXPECT_GT(result.blocksPerSM, 0);
    EXPECT_GT(result.activeWarps, 0);
    EXPECT_GT(result.activeThreads, 0);
    EXPECT_GT(result.occupancyPercent, 0.0f);
    EXPECT_LE(result.occupancyPercent, 100.0f);
}

TEST_F(SchedulingTest, OccupancyWithSharedMemory) {
    OccupancyCalculator calc(0);

    // Test with shared memory usage
    OccupancyResult result1 = calc.calculateOccupancy(256, 0, 0);
    OccupancyResult result2 = calc.calculateOccupancy(256, 4096, 0);

    // With shared memory, occupancy should be lower or equal
    EXPECT_LE(result2.blocksPerSM, result1.blocksPerSM);
}

TEST_F(SchedulingTest, OccupancyWithRegisters) {
    OccupancyCalculator calc(0);

    // Test with register usage
    OccupancyResult result1 = calc.calculateOccupancy(256, 0, 0);
    OccupancyResult result2 = calc.calculateOccupancy(256, 0, 64);

    // With high register usage, occupancy should be lower or equal
    EXPECT_LE(result2.blocksPerSM, result1.blocksPerSM);
}

TEST_F(SchedulingTest, OptimalBlockSizeCalculation) {
    OccupancyCalculator calc(0);

    int optimalSize = calc.getOptimalBlockSize(0);

    EXPECT_GT(optimalSize, 0);
    EXPECT_LE(optimalSize, calc.deviceProps.maxThreadsPerBlock);
    EXPECT_EQ(optimalSize % 32, 0);  // Should be multiple of warp size
}

TEST_F(SchedulingTest, LowResourceKernelWorks) {
    const int N = 1024;
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run kernel
    low_resource_kernel<<<(N+255)/256, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify results
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i] * 2.0f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(SchedulingTest, HighRegisterKernelWorks) {
    const int N = 1024;
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input
    std::vector<float> h_input(N, 1.0f);
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run kernel with high register usage
    high_register_kernel<<<(N+255)/256, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify kernel executed successfully
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    // Just check that results are non-zero
    for (int i = 0; i < N; i++) {
        EXPECT_GT(h_output[i], 0.0f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(SchedulingTest, HighSharedMemoryKernelWorks) {
    const int N = 1024;
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input
    std::vector<float> h_input(N, 1.0f);
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run kernel with 512 floats of shared memory
    high_shared_mem_kernel<512><<<(N+255)/256, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify kernel executed successfully
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    // Results should be averages
    for (int i = 0; i < N; i++) {
        EXPECT_GT(h_output[i], 0.0f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(SchedulingTest, MeasureSchedulingKernelWorks) {
    const int N = 1024;
    float* d_output = cuda_malloc<float>(N);

    measure_scheduling_kernel<<<(N+255)/256, 256>>>(d_output, N);
    CHECK_KERNEL_LAUNCH();

    // Verify results
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        EXPECT_FLOAT_EQ(h_output[i], sqrtf(static_cast<float>(i)));
    }

    cuda_free(d_output);
}

TEST_F(SchedulingTest, GridStrideKernelWorks) {
    const int N = 10000;  // Larger than grid size
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    // Initialize input
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Run with fewer blocks than needed
    grid_stride_kernel<<<32, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify all elements processed
    std::vector<float> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        float expected = sqrtf(h_input[i]) + sinf(h_input[i]);
        EXPECT_NEAR(h_output[i], expected, 1e-5f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(SchedulingTest, WarpSchedulingKernelWorks) {
    const int N = 1024;
    int* d_output = cuda_malloc<int>(N);

    warp_scheduling_kernel<<<(N+255)/256, 256>>>(d_output, N);
    CHECK_KERNEL_LAUNCH();

    // Verify kernel executed successfully
    std::vector<int> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    // Just verify non-zero outputs
    for (int i = 0; i < N; i++) {
        EXPECT_NE(h_output[i], 0);
    }

    cuda_free(d_output);
}

TEST_F(SchedulingTest, DifferentBlockSizesWork) {
    const int N = 1024;
    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i);
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Test different block sizes
    int blockSizes[] = {64, 128, 256, 512};
    for (int blockSize : blockSizes) {
        int gridSize = (N + blockSize - 1) / blockSize;
        low_resource_kernel<<<gridSize, blockSize>>>(d_output, d_input, N);
        CHECK_KERNEL_LAUNCH();

        std::vector<float> h_output(N);
        cuda_memcpy_d2h(h_output.data(), d_output, N);

        for (int i = 0; i < N; i++) {
            EXPECT_FLOAT_EQ(h_output[i], h_input[i] * 2.0f)
                << "Failed with block size " << blockSize << " at index " << i;
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}
