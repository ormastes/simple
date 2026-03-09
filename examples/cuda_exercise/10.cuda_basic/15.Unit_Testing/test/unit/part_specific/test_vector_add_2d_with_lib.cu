// test_vector_add_2d_with_lib.cu - Tests for 2D vector operations using GPU testing framework
// This file demonstrates library-based testing with GPU_TEST_F
#include "gpu_gtest.h"
#include "gtest_generator.h"
#include "cuda_utils.h"  // Use our custom CUDA utilities library
#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <vector>
#include <iostream>

#include "kernels/vector_add_2d.h"


//==================================================//
//     GPU_TEST_F Examples with GpuFixture          //
//==================================================//

// 1. Define DeviceView struct (POD only)
struct VectorAddDeviceView {
    int N;
    float* d_a;
    float* d_b;
    float* d_result;
    float expected_sum;
};

// 2. Create fixture inheriting from GpuFixture<DeviceView>
class VectorAddFixture : public GpuFixture<VectorAddDeviceView> {
protected:
    VectorAddDeviceView h_view;  // Host copy
    VectorAddDeviceView* d_view; // Device copy

    void SetUp() override {
        GpuFixture::SetUp();

        // Initialize host view data
        h_view.N = 1024;
        h_view.d_a = cuda_malloc<float>(h_view.N);
        h_view.d_b = cuda_malloc<float>(h_view.N);
        h_view.d_result = cuda_malloc<float>(h_view.N);
        h_view.expected_sum = 5.0f;

        // Initialize device memory
        std::vector<float> h_a(h_view.N, 2.0f);
        std::vector<float> h_b(h_view.N, 3.0f);
        cuda_memcpy(h_view.d_a, h_a.data(), h_view.N, cudaMemcpyHostToDevice);
        cuda_memcpy(h_view.d_b, h_b.data(), h_view.N, cudaMemcpyHostToDevice);

        // Allocate device view and copy
        d_view = cuda_malloc<VectorAddDeviceView>(1);
        cuda_memcpy(d_view, &h_view, 1, cudaMemcpyHostToDevice);
    }

    void TearDown() override {
        cuda_free(h_view.d_a);
        cuda_free(h_view.d_b);
        cuda_free(h_view.d_result);
        cuda_free(d_view);
        GpuFixture::TearDown();
    }

    const VectorAddDeviceView* device_view() const override {
        return d_view;  // Return device pointer!
    }

    GpuLaunchCfg launch_cfg() const override {
        return MakeLaunchCfg((h_view.N + 255) / 256, 256);
    }
};

// 3. Write GPU test - test body runs on device
GPU_TEST_F(VectorAddFixture, DeviceSideBasicValidation) {
    // _ctx is const VectorAddDeviceView* (device-accessible)
    // This entire test body runs ON THE GPU!

    // Simple test: verify context values are accessible
    GPU_EXPECT_TRUE(_ctx->N == 1024);
    GPU_EXPECT_NEAR(_ctx->expected_sum, 5.0f, 1e-5f);
}

GPU_TEST_F(VectorAddFixture, DeviceSideSquareValidation) {
    // _ctx is const VectorAddDeviceView* (device-accessible)
    // This entire test body runs ON THE GPU!

    GPU_FOR_ALL(i, _ctx->N) {
        // Test square function from library header (must be inline)
        float squared = square(_ctx->d_a[i]);
        GPU_EXPECT_NEAR(squared, 4.0f, 1e-5f);

        // Test element-wise operation
        _ctx->d_result[i] = _ctx->d_a[i] + _ctx->d_b[i];
        GPU_EXPECT_NEAR(_ctx->d_result[i], _ctx->expected_sum, 1e-5f);
    }
}

GPU_TEST_F(VectorAddFixture, DeviceSideThreadIndexing) {
    // Test thread indexing patterns
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < _ctx->N) {
        // Verify thread can access its data
        GPU_EXPECT_TRUE(_ctx->d_a[tid] >= 0.0f);
        GPU_EXPECT_TRUE(_ctx->d_b[tid] >= 0.0f);

        // Test basic computation
        float result = _ctx->d_a[tid] + _ctx->d_b[tid];
        GPU_EXPECT_NEAR(result, _ctx->expected_sum, 1e-5f);
    }
}

// Example with smaller fixture for reduction testing
struct ReductionDeviceView {
    float* data;
    float* result;
    int size;
    float expected_value;
};

class ReductionFixture : public GpuFixture<ReductionDeviceView> {
protected:
    ReductionDeviceView h_view;  // Host copy
    ReductionDeviceView* d_view; // Device copy

    void SetUp() override {
        GpuFixture::SetUp();

        h_view.size = 256;
        h_view.expected_value = 1.0f;
        h_view.data = cuda_malloc<float>(h_view.size);
        h_view.result = cuda_malloc<float>(1);

        // Initialize data
        std::vector<float> h_data(h_view.size, h_view.expected_value);
        cuda_memcpy(h_view.data, h_data.data(), h_view.size, cudaMemcpyHostToDevice);

        // Allocate device view and copy
        d_view = cuda_malloc<ReductionDeviceView>(1);
        cuda_memcpy(d_view, &h_view, 1, cudaMemcpyHostToDevice);
    }

    void TearDown() override {
        cuda_free(h_view.data);
        cuda_free(h_view.result);
        cuda_free(d_view);
        GpuFixture::TearDown();
    }

    const ReductionDeviceView* device_view() const override {
        return d_view;  // Return device pointer!
    }

    GpuLaunchCfg launch_cfg() const override {
        return MakeLaunchCfg(1, h_view.size);
    }
};

GPU_TEST_F(ReductionFixture, ValidateInputData) {
    // Device-side validation of input data
    int tid = threadIdx.x;
    if (tid < _ctx->size) {
        GPU_EXPECT_NEAR(_ctx->data[tid], _ctx->expected_value, 1e-5f);
    }
}

GPU_TEST_F(ReductionFixture, DeviceSideBounds) {
    // Test boundary conditions on device
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    GPU_EXPECT_TRUE(tid >= 0);
    GPU_EXPECT_TRUE(_ctx->size == 256);

    if (tid < _ctx->size) {
        GPU_EXPECT_TRUE(_ctx->data[tid] > 0.0f);
    }
}


//==================================================//
//     GPU_TEST_G Examples with Generators          //
//==================================================//

// Base test class (optional, can be used for shared setup)
class GpuGeneratorWithLibTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Any common setup
    }
};

// Test with ALIGNED mode (round-robin)
GPU_TEST_G(GpuGeneratorWithLibTest, AlignedMode) {
    int x = GPU_GENERATOR(1, 2, 3, 4);
    int y = GPU_GENERATOR(100, 200, 300);
    int z = GPU_GENERATOR(1000, 2000);
    GPU_USE_GENERATOR(ALIGNED);  // Max 4 iterations (max of all generators)

    // In ALIGNED mode:
    // Iteration 0: (1, 100, 1000)
    // Iteration 1: (2, 200, 2000)
    // Iteration 2: (3, 300, 1000) - z wraps around
    // Iteration 3: (4, 100, 2000) - y and z wrap around

    GPU_EXPECT_TRUE(x > 0);
    GPU_EXPECT_TRUE(y >= 100);
    GPU_EXPECT_TRUE(z >= 1000);
}

// Test square function with generators
GPU_TEST_G(GpuGeneratorWithLibTest, square) {
    float a = GPU_GENERATOR(1.0f, 2.0f, 3.0f, 4.0f);
    GPU_USE_GENERATOR();  // Use default FULL mode for single generator

    float result = square(a);
    float expected = a * a;

    GPU_EXPECT_NEAR(result, expected, 1e-5f);
}



// Generator test with custom launch configuration
GPU_TEST_G_CFG(GpuGeneratorWithLibTest, ThreadConfig, 2, 32) {
    int threads = GPU_GENERATOR(32, 64, 128);
    int blocks = GPU_GENERATOR(1, 2, 4);
    GPU_USE_GENERATOR();  // 3 * 3 = 9 combinations

#ifdef __CUDA_ARCH__
    // This test runs with <<<2, 32>>> configuration
    int tid = threadIdx.x + blockIdx.x * blockDim.x;

    if (tid == 0) {
        GPU_EXPECT_TRUE(threads > 0);
        GPU_EXPECT_TRUE(blocks > 0);
        GPU_EXPECT_EQ(threads * blocks, blocks * threads);
    }
#endif
}

// Test with floating point values
GPU_TEST_G(GpuGeneratorWithLibTest, FloatOperations) {
    float scale = GPU_GENERATOR(0.5f, 1.0f, 2.0f);
    float offset = GPU_GENERATOR(-1.0f, 0.0f, 1.0f);
    GPU_USE_GENERATOR();  // 3 * 3 = 9 combinations

    float result = scale * 10.0f + offset;
    float expected_min = scale * 10.0f - 1.1f;
    float expected_max = scale * 10.0f + 1.1f;

    GPU_EXPECT_TRUE(result >= expected_min);
    GPU_EXPECT_TRUE(result <= expected_max);
}

// Complex test with multiple generators
GPU_TEST_G(GpuGeneratorWithLibTest, MatrixDimensions) {
    int rows = GPU_GENERATOR(16, 32, 64);
    int cols = GPU_GENERATOR(8, 16, 32, 64);
    int depth = GPU_GENERATOR(1, 3);
    GPU_USE_GENERATOR();  // 3 * 4 * 2 = 24 combinations

    int total_elements = rows * cols * depth;

    GPU_EXPECT_TRUE(total_elements > 0);
    GPU_EXPECT_TRUE(rows <= 64);
    GPU_EXPECT_TRUE(cols <= 64);
    GPU_EXPECT_EQ(total_elements, rows * cols * depth);
}

// Test with boolean logic
GPU_TEST_G(GpuGeneratorWithLibTest, BooleanLogic) {
    int condition1 = GPU_GENERATOR(0, 1);
    int condition2 = GPU_GENERATOR(0, 1);
    int condition3 = GPU_GENERATOR(0, 1);
    GPU_USE_GENERATOR();  // 2 * 2 * 2 = 8 combinations

    bool c1 = condition1 != 0;
    bool c2 = condition2 != 0;
    bool c3 = condition3 != 0;

    // Test logical operations
    bool and_result = c1 && c2 && c3;
    bool or_result = c1 || c2 || c3;

    if (and_result) {
        GPU_EXPECT_TRUE(c1);
        GPU_EXPECT_TRUE(c2);
        GPU_EXPECT_TRUE(c3);
    }

    if (!or_result) {
        GPU_EXPECT_TRUE(!c1);
        GPU_EXPECT_TRUE(!c2);
        GPU_EXPECT_TRUE(!c3);
    }
}

// Test with grid-stride loop
dim3 block(16, 16);
dim3 grid(4, 4);  // Fixed configuration for this test
GPU_TEST_G_CFG(GpuGeneratorWithLibTest, GridStrideLoop, grid, block) {
    int array_size = GPU_GENERATOR(64, 128, 256);
    int multiplier = GPU_GENERATOR(2, 3);
    GPU_USE_GENERATOR();  // 3 * 2 = 6 combinations

    GPU_FOR_ALL(i, array_size) {
        int value = i * multiplier;
        int expected = i * multiplier;
        GPU_EXPECT_EQ(value, expected);

        if (i == 0) {
            GPU_EXPECT_EQ(value, 0);
        }
    }
}

// Test edge cases
GPU_TEST_G(GpuGeneratorWithLibTest, EdgeCases) {
    int negative = GPU_GENERATOR(-10, -5, -1);
    int zero = GPU_GENERATOR(0);
    int positive = GPU_GENERATOR(1, 5, 10);
    GPU_USE_GENERATOR();  // 3 * 1 * 3 = 9 combinations

    GPU_EXPECT_TRUE(negative < 0);
    GPU_EXPECT_EQ(zero, 0);
    GPU_EXPECT_TRUE(positive > 0);

    // Test arithmetic properties
    GPU_EXPECT_EQ(negative + positive + zero, negative + positive);
    GPU_EXPECT_TRUE(negative * positive < 0);
    GPU_EXPECT_EQ(zero * positive, 0);
}


//==================================================//
//     Host-side Integration Tests with Generators  //
//==================================================//

// Test fixture for host-side generator tests
class HostGeneratorWithLibTest : public ::gtest_generator::TestWithGenerator {
};

TEST_G(HostGeneratorWithLibTest, VectorAdd2D) {
    // Generate different test dimensions
    int width = GENERATOR(16, 32, 64);
    int height = GENERATOR(16, 32, 64);
    float a_value = GENERATOR(1.0f, 2.0f, 3.0f);
    float b_value = GENERATOR(1.0f, 2.0f, 3.0f);
    USE_GENERATOR(ALIGNED);  // Use aligned mode to reduce test count (3 tests instead of 81)

    const int size = width * height;

    // Allocate device memory using our utilities
    float* d_a = cuda_malloc<float>(size);
    float* d_b = cuda_malloc<float>(size);
    float* d_c = cuda_malloc<float>(size);

    // Initialize test data with generated values
    std::vector<float> h_a(size, a_value);
    std::vector<float> h_b(size, b_value);

    // Copy data to device
    cuda_memcpy(d_a, h_a.data(), size, cudaMemcpyHostToDevice);
    cuda_memcpy(d_b, h_b.data(), size, cudaMemcpyHostToDevice);

    // Launch kernel
    dim3 block(16, 16);
    dim3 grid((width + block.x - 1) / block.x, (height + block.y - 1) / block.y);
    vector_add_2d<<<grid, block>>>(d_a, d_b, d_c, width, height);
    cudaDeviceSynchronize();

    // Check results
    std::vector<float> h_c(size);
    cuda_memcpy(h_c.data(), d_c, size, cudaMemcpyDeviceToHost);

    // Expected: a_value + b_value (kernel does simple addition)
    float expected = a_value + b_value;
    for (int i = 0; i < size; i++) {
        EXPECT_NEAR(h_c[i], expected, 1e-5f);
    }

    // Free device memory
    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);
}

TEST_G(HostGeneratorWithLibTest, ReduceSum2D) {
    // Generate test parameters
    int width = GENERATOR(8, 16, 32, 64);
    int height = GENERATOR(8, 16, 32, 64);
    float value = GENERATOR(0.5f, 1.0f, 2.0f, 3.0f);
    int stride = GENERATOR(1, 2);
    USE_GENERATOR(ALIGNED);  // Max of 4 test runs instead of 256

    const int size = width * height;

    // Allocate device memory
    float* d_input = cuda_malloc<float>(size);
    float* d_output = cuda_calloc<float>(1);

    // Initialize with generated value
    std::vector<float> h_input(size, value);
    cuda_memcpy(d_input, h_input.data(), size, cudaMemcpyHostToDevice);

    // Launch reduction kernel with appropriate configuration
    dim3 block(256);  // Use 1D block for reduction
    dim3 grid((size + block.x - 1) / block.x);
    size_t shmem_size = block.x * sizeof(float);
    reduce_sum<<<grid, block, shmem_size>>>(d_input, d_output, size, stride);
    cudaDeviceSynchronize();

    // Check result
    float h_output;
    cuda_memcpy(&h_output, d_output, 1, cudaMemcpyDeviceToHost);

    // Expected sum: value * size (when stride=1)
    // Note: For stride > 1, the actual behavior depends on kernel implementation
    float expected = value * size;
    float tolerance = std::abs(expected) * 1e-4f + 1e-3f;

    EXPECT_NEAR(h_output, expected, tolerance)
        << "Failed for dimensions " << width << "x" << height
        << " with value=" << value << ", stride=" << stride;

    // Free device memory
    cuda_free(d_input);
    cuda_free(d_output);
}