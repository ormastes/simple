/**
 * Multi-GPU Reduction Tests (Module 27)
 *
 * Tests multi-GPU reduction operations
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "multi_gpu_manager.h"
#include <vector>
#include <numeric>

// Kernel declarations
template<int BLOCK_SIZE>
__global__ void reduction_local_multi_gpu(const float*, float*, int);

__global__ void reduction_tree_combine(float*, float*, int);

__global__ void vector_add_multi_gpu(const float*, const float*, float*, int);

class MultiGPUReductionTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        int deviceCount;
        cudaGetDeviceCount(&deviceCount);

        if (deviceCount < 2) {
            GTEST_SKIP() << "Multi-GPU tests require at least 2 GPUs";
        }

        mgr = new MultiGPUManager();
        mgr->setupPeerAccess();
    }

    void TearDown() override {
        delete mgr;
        GpuTest::TearDown();
    }

    MultiGPUManager* mgr;
};

TEST_F(MultiGPUReductionTest, DistributedSum) {
    const int N = 1000000;
    const int BLOCK_SIZE = 256;

    int deviceCount = mgr->getDeviceCount();

    // Create host data
    std::vector<float> h_data(N);
    for (int i = 0; i < N; i++) {
        h_data[i] = 1.0f;  // Simple test: all ones
    }

    float expected_sum = static_cast<float>(N);

    // Distribute data across GPUs
    MultiGPUBuffer<float> d_data(N, *mgr);
    d_data.copyFromHost(h_data.data());

    // Allocate result buffers on each GPU
    std::vector<float*> d_partial_results(deviceCount);
    for (int dev = 0; dev < deviceCount; dev++) {
        cudaSetDevice(dev);
        cudaMalloc(&d_partial_results[dev], sizeof(float));
        cudaMemset(d_partial_results[dev], 0, sizeof(float));
    }

    // Phase 1: Local reduction on each GPU
    for (int dev = 0; dev < deviceCount; dev++) {
        int n_local = d_data.getDeviceSize(dev);
        if (n_local == 0) continue;

        cudaSetDevice(dev);

        int numBlocks = (n_local + BLOCK_SIZE * 4 - 1) / (BLOCK_SIZE * 4);
        reduction_local_multi_gpu<BLOCK_SIZE><<<numBlocks, BLOCK_SIZE,
                                                 0, mgr->getStream(dev)>>>(
            d_data.getDevicePtr(dev),
            d_partial_results[dev],
            n_local);

        CHECK_KERNEL_LAUNCH();
    }

    mgr->synchronizeAll();

    // Phase 2: Gather partial results to GPU 0
    std::vector<float> h_partial_results(deviceCount);
    for (int dev = 0; dev < deviceCount; dev++) {
        cudaSetDevice(dev);
        cudaMemcpy(&h_partial_results[dev], d_partial_results[dev],
                   sizeof(float), cudaMemcpyDeviceToHost);
    }

    // Copy partial results to GPU 0
    cudaSetDevice(0);
    float* d_all_partials;
    cudaMalloc(&d_all_partials, deviceCount * sizeof(float));
    cudaMemcpy(d_all_partials, h_partial_results.data(),
               deviceCount * sizeof(float), cudaMemcpyHostToDevice);

    float* d_final_result;
    cudaMalloc(&d_final_result, sizeof(float));

    // Phase 3: Final reduction on GPU 0
    reduction_tree_combine<<<1, 256>>>(d_all_partials, d_final_result, deviceCount);
    CHECK_KERNEL_LAUNCH();

    // Get final result
    float final_sum;
    cudaMemcpy(&final_sum, d_final_result, sizeof(float), cudaMemcpyDeviceToHost);

    printf("Expected sum: %.1f, Got: %.1f\n", expected_sum, final_sum);
    EXPECT_NEAR(final_sum, expected_sum, 1.0f);

    // Cleanup
    for (int dev = 0; dev < deviceCount; dev++) {
        cudaSetDevice(dev);
        cudaFree(d_partial_results[dev]);
    }
    cudaSetDevice(0);
    cudaFree(d_all_partials);
    cudaFree(d_final_result);
}

TEST_F(MultiGPUReductionTest, VectorAddition) {
    const int N = 100000;
    int deviceCount = mgr->getDeviceCount();

    // Create host data
    std::vector<float> h_a(N), h_b(N), h_c(N), h_c_ref(N);

    for (int i = 0; i < N; i++) {
        h_a[i] = static_cast<float>(i);
        h_b[i] = static_cast<float>(i * 2);
        h_c_ref[i] = h_a[i] + h_b[i];
    }

    // Distribute across GPUs
    MultiGPUBuffer<float> d_a(N, *mgr);
    MultiGPUBuffer<float> d_b(N, *mgr);
    MultiGPUBuffer<float> d_c(N, *mgr);

    d_a.copyFromHost(h_a.data());
    d_b.copyFromHost(h_b.data());

    // Launch vector add on each GPU
    for (int dev = 0; dev < deviceCount; dev++) {
        int n_local = d_a.getDeviceSize(dev);
        if (n_local == 0) continue;

        cudaSetDevice(dev);

        int numBlocks = (n_local + 255) / 256;
        vector_add_multi_gpu<<<numBlocks, 256, 0, mgr->getStream(dev)>>>(
            d_a.getDevicePtr(dev),
            d_b.getDevicePtr(dev),
            d_c.getDevicePtr(dev),
            n_local);

        CHECK_KERNEL_LAUNCH();
    }

    mgr->synchronizeAll();

    // Get results
    d_c.copyToHost(h_c.data());

    // Verify
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_c[i], h_c_ref[i], 1e-5f)
            << "Mismatch at index " << i;
    }
}

TEST_F(MultiGPUReductionTest, MultiBufferAllocation) {
    const int N = 1000000;

    MultiGPUBuffer<float> buffer(N, *mgr);

    // Verify distribution
    size_t totalAllocated = 0;
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        size_t devSize = buffer.getDeviceSize(dev);
        EXPECT_GT(devSize, 0) << "GPU " << dev << " has no data";
        totalAllocated += devSize;

        printf("GPU %d: %zu elements\n", dev, devSize);
    }

    EXPECT_EQ(totalAllocated, N) << "Total allocation mismatch";
}
