// test_memory_types.cu - Comprehensive tests for all CUDA memory types
// Tests both explicit and implicit usage of each memory type
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

// Include the kernels from memory_types_demo.cu
extern "C" {
    // Registers
    __global__ void register_implicit(const float* input, float* output, int N);
    __global__ void register_explicit(const float* input, float* output, int N);
    __global__ void register_unrolled(const float* input, float* output, int N);

    // Shared memory
    __global__ void shared_static(const float* input, float* output, int N);
    __global__ void shared_dynamic(const float* input, float* output, int N);
    __global__ void shared_padded(const float* input, float* output, int N);

    // Constant memory
    __global__ void constant_explicit(const float* input, float* output, int N);
    void set_constant_memory_demo(float scalar, const float* coeffs, int coeff_size);

    // Texture memory
    __global__ void texture_1d_explicit(cudaTextureObject_t texObj, float* output, int N);
    __global__ void texture_2d_explicit(cudaTextureObject_t texObj, float* output,
                                        int width, int height);
    cudaTextureObject_t create_texture_1d(const float* d_data, int N);
    cudaTextureObject_t create_texture_2d(cudaArray_t array);

    // Global memory
    __global__ void global_implicit(const float* input, float* output, int N);
    __global__ void global_coalesced(const float* input, float* output, int N);
    __global__ void global_strided(const float* input, float* output, int N, int stride);

    // L1 Cache
    __global__ void l1_cache_implicit(const float* input, float* output, int N);
    __global__ void l1_cache_prefer_l1(const float* input, float* output, int N);
    void configure_l1_cache(cudaFuncCache preference);

    // L2 Cache
    __global__ void l2_cache_implicit(const float* input, float* output, int N);
}

// ============================================================================
// Test Fixture
// ============================================================================

class MemoryTypesTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
        N = 1024;
        bytes = N * sizeof(float);

        // Allocate host memory
        h_input.resize(N);
        h_output.resize(N);

        // Initialize input
        for (int i = 0; i < N; i++) {
            h_input[i] = static_cast<float>(i);
        }

        // Allocate device memory
        d_input = cuda_malloc<float>(N);
        d_output = cuda_malloc<float>(N);

        // Copy to device
        cudaMemcpy(d_input, h_input.data(), bytes, cudaMemcpyHostToDevice);
    }

    void TearDown() override {
        cuda_free(d_input);
        cuda_free(d_output);
        GpuTest::TearDown();
    }

    void VerifyOutput(float (*expected_fn)(float)) {
        cudaMemcpy(h_output.data(), d_output, bytes, cudaMemcpyDeviceToHost);
        for (int i = 0; i < N; i++) {
            EXPECT_NEAR(h_output[i], expected_fn(h_input[i]), 1e-5f)
                << "Mismatch at index " << i;
        }
    }

    int N;
    size_t bytes;
    std::vector<float> h_input;
    std::vector<float> h_output;
    float* d_input;
    float* d_output;
};

// ============================================================================
// 1. REGISTER MEMORY TESTS
// ============================================================================

TEST_F(MemoryTypesTest, RegisterImplicitUsage) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    register_implicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f + 1.0f; });
}

TEST_F(MemoryTypesTest, RegisterExplicitUsage) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    register_explicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f + 1.0f; });
}

TEST_F(MemoryTypesTest, RegisterUnrolledUsage) {
    dim3 block(256);
    dim3 grid((N + block.x * 4 - 1) / (block.x * 4));

    cudaMemset(d_output, 0, bytes);
    register_unrolled<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f + 1.0f; });
}

// ============================================================================
// 2. SHARED MEMORY TESTS
// ============================================================================

TEST_F(MemoryTypesTest, SharedMemoryStatic) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    shared_static<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

TEST_F(MemoryTypesTest, SharedMemoryDynamic) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);
    size_t shared_mem = block.x * sizeof(float);

    shared_dynamic<<<grid, block, shared_mem>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

TEST_F(MemoryTypesTest, SharedMemoryPadded) {
    int width = 32;
    int height = 32;
    dim3 block(32, 32);
    dim3 grid(1, 1);

    // Reallocate for 2D test
    cuda_free(d_input);
    cuda_free(d_output);
    d_input = cuda_malloc<float>(width * height);
    d_output = cuda_malloc<float>(width * height);

    std::vector<float> input_2d(width * height);
    for (int i = 0; i < width * height; i++) {
        input_2d[i] = static_cast<float>(i);
    }
    cudaMemcpy(d_input, input_2d.data(), width * height * sizeof(float),
               cudaMemcpyHostToDevice);

    shared_padded<<<grid, block>>>(d_input, d_output, width);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> output_2d(width * height);
    cudaMemcpy(output_2d.data(), d_output, width * height * sizeof(float),
               cudaMemcpyDeviceToHost);

    for (int i = 0; i < width * height; i++) {
        EXPECT_NEAR(output_2d[i], input_2d[i] * 2.0f, 1e-5f);
    }
}

// ============================================================================
// 3. CONSTANT MEMORY TESTS
// ============================================================================

TEST_F(MemoryTypesTest, ConstantMemoryExplicit) {
    // Set constant memory
    float scalar = 2.0f;
    std::vector<float> coeffs(16);
    for (int i = 0; i < 16; i++) {
        coeffs[i] = 0.1f * i;
    }
    set_constant_memory_demo(scalar, coeffs.data(), 16);

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    constant_explicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    // Expected: input * 2.0 + sum(coeffs)
    float coeff_sum = 0.0f;
    for (int i = 0; i < 16; i++) {
        coeff_sum += coeffs[i];
    }

    VerifyOutput([scalar, coeff_sum](float x) {
        return x * scalar + coeff_sum;
    });
}

// ============================================================================
// 4. TEXTURE MEMORY TESTS
// ============================================================================

TEST_F(MemoryTypesTest, TextureMemory1D) {
    // Create 1D texture
    cudaTextureObject_t texObj = create_texture_1d(d_input, N);
    ASSERT_NE(texObj, 0);

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    texture_1d_explicit<<<grid, block>>>(texObj, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });

    cudaDestroyTextureObject(texObj);
}

TEST_F(MemoryTypesTest, TextureMemory2D) {
    int width = 32;
    int height = 32;

    // Create 2D CUDA array
    cudaChannelFormatDesc channelDesc = cudaCreateChannelDesc<float>();
    cudaArray_t cuArray;
    cudaMallocArray(&cuArray, &channelDesc, width, height);

    std::vector<float> input_2d(width * height);
    for (int i = 0; i < width * height; i++) {
        input_2d[i] = static_cast<float>(i);
    }
    cudaMemcpy2DToArray(cuArray, 0, 0, input_2d.data(), width * sizeof(float),
                        width * sizeof(float), height, cudaMemcpyHostToDevice);

    // Create texture object
    cudaTextureObject_t texObj = create_texture_2d(cuArray);
    ASSERT_NE(texObj, 0);

    // Allocate output
    float* d_output_2d = cuda_malloc<float>(width * height);

    dim3 block(16, 16);
    dim3 grid((width + block.x - 1) / block.x, (height + block.y - 1) / block.y);

    texture_2d_explicit<<<grid, block>>>(texObj, d_output_2d, width, height);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> output_2d(width * height);
    cudaMemcpy(output_2d.data(), d_output_2d, width * height * sizeof(float),
               cudaMemcpyDeviceToHost);

    for (int i = 0; i < width * height; i++) {
        EXPECT_NEAR(output_2d[i], input_2d[i] * 2.0f, 1e-5f);
    }

    cudaDestroyTextureObject(texObj);
    cudaFreeArray(cuArray);
    cuda_free(d_output_2d);
}

// ============================================================================
// 5. GLOBAL MEMORY TESTS
// ============================================================================

TEST_F(MemoryTypesTest, GlobalMemoryImplicit) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    global_implicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

TEST_F(MemoryTypesTest, GlobalMemoryCoalesced) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    global_coalesced<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

TEST_F(MemoryTypesTest, GlobalMemoryStrided) {
    int stride = 2;
    dim3 block(256);
    dim3 grid((N / stride + block.x - 1) / block.x);

    cudaMemset(d_output, 0, bytes);
    global_strided<<<grid, block>>>(d_input, d_output, N, stride);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_output.data(), d_output, bytes, cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        if (i % stride == 0) {
            EXPECT_NEAR(h_output[i], h_input[i] * 2.0f, 1e-5f);
        } else {
            EXPECT_FLOAT_EQ(h_output[i], 0.0f);
        }
    }
}

// ============================================================================
// 6. L1 CACHE TESTS (Implicit - behavior verification)
// ============================================================================

TEST_F(MemoryTypesTest, L1CacheImplicit) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    l1_cache_implicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

TEST_F(MemoryTypesTest, L1CachePreferL1) {
    // Configure L1 preference
    configure_l1_cache(cudaFuncCachePreferL1);

    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    l1_cache_prefer_l1<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });

    // Reset to default
    configure_l1_cache(cudaFuncCachePreferNone);
}

// ============================================================================
// 7. L2 CACHE TESTS (Implicit - behavior verification)
// ============================================================================

TEST_F(MemoryTypesTest, L2CacheImplicit) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    l2_cache_implicit<<<grid, block>>>(d_input, d_output, N);
    CHECK_KERNEL_LAUNCH();

    VerifyOutput([](float x) { return x * 2.0f; });
}

// ============================================================================
// PERFORMANCE COMPARISON TESTS
// ============================================================================

class MemoryTypesPerformanceTest : public MemoryTypesTest {
protected:
    void BenchmarkKernel(const char* name, std::function<void()> kernel_launcher,
                        int iterations = 100) {
        // Warmup
        kernel_launcher();
        cudaDeviceSynchronize();

        // Benchmark
        cudaEvent_t start, stop;
        cudaEventCreate(&start);
        cudaEventCreate(&stop);

        cudaEventRecord(start);
        for (int i = 0; i < iterations; i++) {
            kernel_launcher();
        }
        cudaEventRecord(stop);
        cudaEventSynchronize(stop);

        float milliseconds = 0;
        cudaEventElapsedTime(&milliseconds, start, stop);

        float avg_time = milliseconds / iterations;
        float bandwidth = (N * sizeof(float) * 2) / (avg_time / 1000.0f) / 1e9;

        printf("%s: %.3f ms, %.2f GB/s\n", name, avg_time, bandwidth);

        cudaEventDestroy(start);
        cudaEventDestroy(stop);
    }
};

TEST_F(MemoryTypesPerformanceTest, CompareRegisterUsage) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    BenchmarkKernel("Register Implicit", [&]() {
        register_implicit<<<grid, block>>>(d_input, d_output, N);
    });

    BenchmarkKernel("Register Unrolled (4x)", [&]() {
        dim3 grid_unroll((N + block.x * 4 - 1) / (block.x * 4));
        register_unrolled<<<grid_unroll, block>>>(d_input, d_output, N);
    });
}

TEST_F(MemoryTypesPerformanceTest, CompareMemoryAccess) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    BenchmarkKernel("Global Memory", [&]() {
        global_implicit<<<grid, block>>>(d_input, d_output, N);
    });

    BenchmarkKernel("Shared Memory Static", [&]() {
        shared_static<<<grid, block>>>(d_input, d_output, N);
    });

    size_t shared_mem = block.x * sizeof(float);
    BenchmarkKernel("Shared Memory Dynamic", [&]() {
        shared_dynamic<<<grid, block, shared_mem>>>(d_input, d_output, N);
    });
}

TEST_F(MemoryTypesPerformanceTest, CompareCoalescingImpact) {
    dim3 block(256);
    dim3 grid((N + block.x - 1) / block.x);

    BenchmarkKernel("Coalesced Access", [&]() {
        global_coalesced<<<grid, block>>>(d_input, d_output, N);
    });

    int stride = 2;
    dim3 grid_strided((N / stride + block.x - 1) / block.x);
    BenchmarkKernel("Strided Access (stride=2)", [&]() {
        global_strided<<<grid_strided, block>>>(d_input, d_output, N, stride);
    });
}
