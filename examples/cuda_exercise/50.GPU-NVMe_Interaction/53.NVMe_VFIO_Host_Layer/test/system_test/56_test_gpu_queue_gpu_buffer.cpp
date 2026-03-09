/**
 * @file 56_test_gpu_queue_gpu_buffer.cpp
 * @brief Module 56 system tests: GPU queue + GPU buffer scaffolding.
 *
 * Validates that SetupHelper can configure GPUDirect queues and GPU buffer pools,
 * mirroring the Module 56 pipeline. GPU kernels are used to emulate the
 * read/write/verify flow names used in Module 53.
 */

// Enable debug logging for test actions
#define DEBUG_LOG_ENABLED 1

#include <cuda_runtime.h>
#include <gtest/gtest.h>

#include <chrono>
#include <numeric>
#include <vector>

#include "cuda_utils.h"
#include "helper/log_helper.h"
#include "helper/setup_helper.h"
#include "memory/cuda_gpu_memory_buffer.h"
#include "queue/nvme_queue.h"

namespace {

__global__ void fill_pattern_kernel(uint8_t* data, size_t bytes, uint8_t seed) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < bytes) {
        data[idx] = static_cast<uint8_t>((seed + idx) & 0xFF);
    }
}

__global__ void zero_kernel(uint8_t* data, size_t bytes) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < bytes) {
        data[idx] = 0;
    }
}

class GpuQueueGpuBufferSystemTest : public ::testing::Test {
protected:
    void SetUp() override {
        const char* bdf = std::getenv("NVME_BDF");
        CHECK_SKIP(bdf && std::strlen(bdf) > 0,
                   "NVME_BDF not set. Export NVME_BDF to run Module 56 tests.");

        cudaError_t err = cudaGetDeviceCount(&gpu_count_);
        CHECK_SKIP(err == cudaSuccess && gpu_count_ > 0, "No CUDA devices available.");

        DEBUG_LOG("CUDA GPU count: %d", gpu_count_);

        helper_.set_arg("bdf", bdf);
        helper_.set_arg("NVME_BDF", bdf);

        helper_.add_task(new VfioBindingTask());
        helper_.add_task(new NvmeSetupTask(bdf, 64, 64, 512));
        helper_.add_task(new GpuDetectionTask());
        helper_.add_task(new GpuP2PSetupTask());
        helper_.add_task(new CudaGpuMemoryFactoryTask(4096, 4));
        helper_.add_task(new DbcDaemonTask("shadow"));  // Ensure shadow doorbells/daemon available for GPU doorbells

        CHECK_SKIP_CLEANUP(
            helper_.setup_all(),
            {},
            "SetupHelper failed to configure GPU queue and buffer pools."
        );

        gpu_queue_ = helper_.get<NvmeQueueStruct*>("gpu_queue");
        gpu_pool_ = helper_.get<CudaGpuPool*>("cuda_gpu_pool");

        DEBUG_LOG("GPU resources initialized: queue=%p, pool=%p", gpu_queue_, gpu_pool_);
    }

    void TearDown() override {
        gpu_queue_ = nullptr;
        gpu_pool_ = nullptr;
    }

    static void copy_to_host(std::vector<uint8_t>& host, const void* device, size_t bytes) {
        host.resize(bytes);
        cudaMemcpy(host.data(), device, bytes, cudaMemcpyDeviceToHost);
    }

    static void run_fill_kernel(DmaBuf* buf, uint8_t seed) {
        const int threads = 256;
        const int blocks = static_cast<int>((buf->bytes + threads - 1) / threads);
        fill_pattern_kernel<<<blocks, threads>>>(static_cast<uint8_t*>(buf->addr), buf->bytes, seed);
        cudaDeviceSynchronize();
    }

    int gpu_count_{0};
    SetupHelper helper_;
    NvmeQueueStruct* gpu_queue_{nullptr};
    CudaGpuPool* gpu_pool_{nullptr};
};

}  // namespace

TEST_F(GpuQueueGpuBufferSystemTest, DeviceInitialization) {
    ASSERT_NE(gpu_queue_, nullptr) << "GPU queue should be allocated";

    EXPECT_GT(gpu_queue_->sq_depth, 0u);
    EXPECT_GT(gpu_queue_->cq_depth, 0u);
    EXPECT_GE(gpu_queue_->qid, 1u);
    EXPECT_NE(gpu_queue_->sq_base, nullptr);
    EXPECT_NE(gpu_queue_->cq_base, nullptr);
    EXPECT_NE(gpu_queue_->sq_addr, nullptr);
    EXPECT_NE(gpu_queue_->cq_addr, nullptr);
    EXPECT_GT(gpu_queue_->nsid, 0u);
    EXPECT_GT(gpu_queue_->page_size, 0u);
    EXPECT_EQ(gpu_queue_->sq_tail, 0u);
    EXPECT_EQ(gpu_queue_->cq_head, 0u);
}

TEST_F(GpuQueueGpuBufferSystemTest, PoolCreationAndManagement) {
    ASSERT_NE(gpu_pool_, nullptr);
    EXPECT_EQ(gpu_pool_->cap, 4);
    EXPECT_GT(gpu_pool_->buf_size, 0u);

    std::vector<DmaBuf*> buffers;
    for (int i = 0; i < gpu_pool_->cap; ++i) {
        DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
        ASSERT_NE(buf, nullptr);
        buffers.push_back(buf);
    }

    for (auto* buf : buffers) {
        cuda_gpu_pool_release(gpu_pool_, buf);
    }
}

TEST_F(GpuQueueGpuBufferSystemTest, SingleBlockRead) {
    DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
    ASSERT_NE(buf, nullptr);

    const size_t bytes = buf->bytes;
    zero_kernel<<<(bytes + 255) / 256, 256>>>(static_cast<uint8_t*>(buf->addr), bytes);
    cudaDeviceSynchronize();

    std::vector<uint8_t> host;
    copy_to_host(host, buf->addr, std::min<size_t>(bytes, 64));
    for (uint8_t value : host) {
        EXPECT_EQ(value, 0u);
    }

    cuda_gpu_pool_release(gpu_pool_, buf);
}

TEST_F(GpuQueueGpuBufferSystemTest, WriteReadVerifySequential) {
    DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
    ASSERT_NE(buf, nullptr);

    run_fill_kernel(buf, 0x10);

    std::vector<uint8_t> host;
    copy_to_host(host, buf->addr, std::min<size_t>(buf->bytes, 256));
    for (size_t i = 0; i < host.size(); ++i) {
        EXPECT_EQ(host[i], static_cast<uint8_t>((0x10 + i) & 0xFF));
    }

    cuda_gpu_pool_release(gpu_pool_, buf);
}

TEST_F(GpuQueueGpuBufferSystemTest, MultipleOutstandingCommands) {
    const int operations = 3;
    std::vector<DmaBuf*> buffers;
    for (int i = 0; i < operations; ++i) {
        DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
        ASSERT_NE(buf, nullptr);
        buffers.push_back(buf);
    }

    std::vector<cudaStream_t> streams(operations);
    for (int i = 0; i < operations; ++i) {
        cudaStreamCreate(&streams[i]);
        const int threads = 256;
        const int blocks = static_cast<int>((buffers[i]->bytes + threads - 1) / threads);
        fill_pattern_kernel<<<blocks, threads, 0, streams[i]>>>(
            static_cast<uint8_t*>(buffers[i]->addr), buffers[i]->bytes,
            static_cast<uint8_t>(0x20 + i));
    }

    for (auto stream : streams) {
        cudaStreamSynchronize(stream);
        cudaStreamDestroy(stream);
    }

    for (int i = 0; i < operations; ++i) {
        std::vector<uint8_t> host;
        copy_to_host(host, buffers[i]->addr, std::min<size_t>(buffers[i]->bytes, 32));
        for (size_t idx = 0; idx < host.size(); ++idx) {
            EXPECT_EQ(host[idx], static_cast<uint8_t>((0x20 + i + idx) & 0xFF));
        }
        cuda_gpu_pool_release(gpu_pool_, buffers[i]);
    }
}

TEST_F(GpuQueueGpuBufferSystemTest, ErrorHandlingInvalidSLBA) {
    std::vector<DmaBuf*> buffers;
    for (int i = 0; i < gpu_pool_->cap; ++i) {
        buffers.push_back(cuda_gpu_pool_acquire(gpu_pool_));
    }

    DmaBuf* extra = cuda_gpu_pool_acquire(gpu_pool_);
    EXPECT_EQ(extra, nullptr) << "Pool should not hand out more buffers than capacity";

    for (auto* buf : buffers) {
        cuda_gpu_pool_release(gpu_pool_, buf);
    }
}

TEST_F(GpuQueueGpuBufferSystemTest, PerformanceSequentialRead) {
    const uint16_t num_iterations = 500;
    DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
    ASSERT_NE(buf, nullptr);

    std::vector<uint8_t> host(buf->bytes);
    test_log::log_benchmark_config(num_iterations, buf->bytes);

    auto start = std::chrono::high_resolution_clock::now();
    for (uint16_t i = 0; i < num_iterations; ++i) {
        zero_kernel<<<(buf->bytes + 255) / 256, 256>>>(static_cast<uint8_t*>(buf->addr), buf->bytes);
        cudaDeviceSynchronize();
        cudaMemcpy(host.data(), buf->addr, buf->bytes, cudaMemcpyDeviceToHost);
    }
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    test_log::calculate_and_log_performance(duration.count(), num_iterations, buf->bytes);
    cuda_gpu_pool_release(gpu_pool_, buf);
}

TEST_F(GpuQueueGpuBufferSystemTest, PerformanceSequentialWrite) {
    const uint16_t num_iterations = 500;
    DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
    ASSERT_NE(buf, nullptr);

    std::vector<uint8_t> host(buf->bytes, 0xCD);
    test_log::log_benchmark_config(num_iterations, buf->bytes);

    auto start = std::chrono::high_resolution_clock::now();
    for (uint16_t i = 0; i < num_iterations; ++i) {
        cudaMemcpy(buf->addr, host.data(), buf->bytes, cudaMemcpyHostToDevice);
        cudaDeviceSynchronize();
    }
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    test_log::calculate_and_log_performance(duration.count(), num_iterations, buf->bytes);
    cuda_gpu_pool_release(gpu_pool_, buf);
}

TEST_F(GpuQueueGpuBufferSystemTest, PerformanceLatencyDistribution) {
    const uint16_t num_samples = 500;
    DmaBuf* buf = cuda_gpu_pool_acquire(gpu_pool_);
    ASSERT_NE(buf, nullptr);

    std::vector<double> latencies;
    latencies.reserve(num_samples);

    for (uint16_t i = 0; i < num_samples; ++i) {
        auto start = std::chrono::high_resolution_clock::now();
        run_fill_kernel(buf, static_cast<uint8_t>(i));
        auto end = std::chrono::high_resolution_clock::now();
        double latency_us = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() / 1000.0;
        latencies.push_back(latency_us);
    }

    test_log::calculate_and_log_latency_stats(latencies);
    cuda_gpu_pool_release(gpu_pool_, buf);
}

TEST_F(GpuQueueGpuBufferSystemTest, PerformanceQueueDepthScaling) {
    const uint16_t max_qd = 4;
    const uint16_t ops_per_qd = 200;
    std::vector<DmaBuf*> bufs;
    for (uint16_t i = 0; i < max_qd; ++i) {
        bufs.push_back(cuda_gpu_pool_acquire(gpu_pool_));
    }

    for (uint16_t qd = 1; qd <= max_qd; ++qd) {
        uint16_t total_ops = qd * ops_per_qd;
        std::vector<cudaStream_t> streams(qd);
        for (uint16_t i = 0; i < qd; ++i) {
            cudaStreamCreate(&streams[i]);
        }

        auto start = std::chrono::high_resolution_clock::now();
        for (uint16_t i = 0; i < total_ops; ++i) {
            uint16_t idx = i % qd;
            const int threads = 256;
            const int blocks = static_cast<int>((bufs[idx]->bytes + threads - 1) / threads);
            fill_pattern_kernel<<<blocks, threads, 0, streams[idx]>>>(
                static_cast<uint8_t*>(bufs[idx]->addr), bufs[idx]->bytes,
                static_cast<uint8_t>(0x40 + idx));
        }
        for (auto stream : streams) {
            cudaStreamSynchronize(stream);
            cudaStreamDestroy(stream);
        }
        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        test_log::calculate_and_log_qd_result(duration.count(), qd, total_ops, bufs[0]->bytes);
    }

    for (auto* buf : bufs) {
        cuda_gpu_pool_release(gpu_pool_, buf);
    }
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    bool listing_only = ::testing::GTEST_FLAG(list_tests);

    printf("\n============================================================\n");
    printf("Module 56: GPU Queue + GPU Buffer System Tests\n");
    printf("============================================================\n\n");

    if (!listing_only) {
        printf("Environment:\n");
        test_log::log_env_var("NVME_BDF", std::getenv("NVME_BDF"));
        printf("Note: GpuP2PSetupTask creates a fallback GPU queue if /dev/gpu_p2p_nvme is unavailable.\n\n");
    }

    int result = RUN_ALL_TESTS();

    printf("\n============================================================\n");
    printf("Module 56 GPU Queue + GPU Buffer Tests Complete\n");
    printf("============================================================\n\n");

    return result;
}
