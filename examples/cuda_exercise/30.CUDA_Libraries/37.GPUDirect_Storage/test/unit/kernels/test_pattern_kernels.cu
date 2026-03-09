#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "pattern_generator.h"
#include <cuda_runtime.h>
#include <vector>

class PatternKernelTest : public GpuTest {};

TEST_F(PatternKernelTest, GenerateSequentialPattern) {
    const size_t size = 1024;
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate pattern starting at offset 0
    launchGeneratePattern(d_data, size, 0, 0);
    cudaDeviceSynchronize();

    // Verify on host
    std::vector<uint8_t> h_data(size);
    cudaMemcpy(h_data.data(), d_data, size, cudaMemcpyDeviceToHost);

    for (size_t i = 0; i < size; i++) {
        EXPECT_EQ(h_data[i], i % 256);
    }

    cudaFree(d_data);
}

TEST_F(PatternKernelTest, GeneratePatternWithOffset) {
    const size_t size = 2048;
    const size_t offset = 1000;
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate pattern starting at offset 1000
    launchGeneratePattern(d_data, size, offset, 0);
    cudaDeviceSynchronize();

    // Verify on host
    std::vector<uint8_t> h_data(size);
    cudaMemcpy(h_data.data(), d_data, size, cudaMemcpyDeviceToHost);

    for (size_t i = 0; i < size; i++) {
        uint8_t expected = static_cast<uint8_t>((offset + i) % 256);
        EXPECT_EQ(h_data[i], expected);
    }

    cudaFree(d_data);
}

TEST_F(PatternKernelTest, VerifyCorrectPattern) {
    const size_t size = 2048;
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate pattern
    launchGeneratePattern(d_data, size, 0, 0);
    cudaDeviceSynchronize();

    // Verify pattern (should have 0 mismatches)
    int mismatches = launchVerifyPattern(d_data, size, 0, 0);
    EXPECT_EQ(mismatches, 0);

    cudaFree(d_data);
}

TEST_F(PatternKernelTest, DetectSingleCorruption) {
    const size_t size = 1024;
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate pattern
    launchGeneratePattern(d_data, size, 0, 0);
    cudaDeviceSynchronize();

    // Corrupt one byte on host
    std::vector<uint8_t> h_data(size);
    cudaMemcpy(h_data.data(), d_data, size, cudaMemcpyDeviceToHost);
    h_data[512] = 0xFF;  // Corrupt byte 512
    cudaMemcpy(d_data, h_data.data(), size, cudaMemcpyHostToDevice);

    // Verify should detect 1 mismatch
    int mismatches = launchVerifyPattern(d_data, size, 0, 0);
    EXPECT_EQ(mismatches, 1);

    cudaFree(d_data);
}

TEST_F(PatternKernelTest, DetectMultipleCorruptions) {
    const size_t size = 4096;
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate pattern
    launchGeneratePattern(d_data, size, 0, 0);
    cudaDeviceSynchronize();

    // Corrupt multiple bytes
    std::vector<uint8_t> h_data(size);
    cudaMemcpy(h_data.data(), d_data, size, cudaMemcpyDeviceToHost);
    h_data[100] = 0xFF;
    h_data[500] = 0xFF;
    h_data[1000] = 0xFF;
    h_data[2000] = 0xFF;
    h_data[3000] = 0xFF;
    cudaMemcpy(d_data, h_data.data(), size, cudaMemcpyHostToDevice);

    // Verify should detect 5 mismatches
    int mismatches = launchVerifyPattern(d_data, size, 0, 0);
    EXPECT_EQ(mismatches, 5);

    cudaFree(d_data);
}

TEST_F(PatternKernelTest, LargeBuffer) {
    const size_t size = 16 * 1024 * 1024;  // 16 MB
    uint8_t* d_data;
    cudaMalloc(&d_data, size);

    // Generate and verify large buffer
    launchGeneratePattern(d_data, size, 0, 0);
    cudaDeviceSynchronize();

    int mismatches = launchVerifyPattern(d_data, size, 0, 0);
    EXPECT_EQ(mismatches, 0);

    cudaFree(d_data);
}
