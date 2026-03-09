/**
 * @file test_cuda_host_io_system.cpp
 * @brief System tests for Module 54: CUDA Host-Pinned Memory integration with NVMe
 *
 * Tests CUDA host memory allocation, registration, and NVMe I/O operations
 * using CUDA-pinned buffers for optimal GPU-NVMe data transfer performance.
 *
 * @author Generated for Module 54
 * @date 2025-11-11
 */

// Enable debug logging for test actions
#define DEBUG_LOG_ENABLED 1

#include <gtest/gtest.h>
#include <cuda_runtime.h>

#include <cstdlib>
#include <cstring>
#include <chrono>
#include <vector>
#include <algorithm>
#include <memory>
#include <string>

#include "cuda_utils.h"  // For DEBUG_LOG

// Module 53 APIs
#include "common/forward_decls.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "doorbell/nvme_doorbell.h"
#include "common/patterns/data_patterns.h"
#include "helper/system_test_config.h"
#include "helper/host_io_test_utils.h"

// Module 54 APIs (CUDA host memory)
#include "cuda_host/io/cuda_io_host_mem.h"

// Test helpers
#include "device/device_detector.h"
#include "device/device_detector.h"
#include "helper/setup_helper.h"
#include "helper/log_helper.h"

using nvme_test::HostTestConfig;
using nvme_test::HostPoolGuard;
using nvme_test::IoContext;
using nvme_test::ScopedDmaBuf;
using nvme_test::select_test_devices;

// ============================================================================
// CUDA Device Check Fixture
// ============================================================================

class CudaHostSystemTest : public ::testing::Test {
protected:
    bool cuda_available_{false};
    int cuda_device_count_{0};
    HostTestConfig config;
    SystemFeatures detected_features_;
    SelectedDevices selected_devices_;
    std::string skip_reason_;
    bool auto_config_attempted_{false};

    std::unique_ptr<SetupHelper> setup_helper_;
    NvmeDevice* dev{nullptr};
    Queue* iosq{nullptr};
    Queue* iocq{nullptr};

    void SetUp() override {
        setup_helper_.reset();

        cudaError_t err = cudaGetDeviceCount(&cuda_device_count_);
        cuda_available_ = (err == cudaSuccess && cuda_device_count_ > 0);
        CHECK_SKIP(cuda_available_, "No CUDA device available. Module 54 tests require CUDA GPU.");

        DEBUG_LOG("CUDA Device Count: %d", cuda_device_count_);

        config.load_from_env(nullptr, false);
        auto_config_attempted_ = true;
        std::string context = config.is_valid()
            ? "Validating provided NVME_BDF. "
            : "NVME_BDF not provided. ";

        CHECK_SKIP_CLEANUP(
            select_test_devices(detected_features_, selected_devices_, skip_reason_, config.bdf),
            {
                skip_reason_ = context + skip_reason_;
                setup_helper_.reset();
            },
            skip_reason_
        );

        config.load_from_env(&selected_devices_);

        setup_helper_ = std::make_unique<SetupHelper>();
        setup_helper_->set_global_args(config.get_setup_args());
        setup_helper_->add_task(new NvmeSetupTask());

        CHECK_SKIP_CLEANUP(
            setup_helper_->setup_all(),
            setup_helper_.reset(),
            "SetupHelper failed to configure NVMe device."
        );

        CHECK_SKIP_CLEANUP(
            (dev = setup_helper_->get<NvmeDevice*>("nvme_device")) != nullptr,
            setup_helper_.reset(),
            "SetupHelper did not return nvme_device handle."
        );

        iosq = nvme_get_iosq(dev);
        iocq = nvme_get_iocq(dev);
        DEBUG_LOG("Device initialized: SQ=%p CQ=%p", iosq, iocq);
    }

    void TearDown() override {
        iosq = nullptr;
        iocq = nullptr;
        dev = nullptr;
        setup_helper_.reset();
    }

    IoContext ioContext() const {
        return IoContext{dev, iosq, iocq, &config};
    }
};

// ============================================================================
// Test Cases
// ============================================================================

TEST_F(CudaHostSystemTest, CudaDeviceInitialization) {
    // Get CUDA device properties
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, 0);

    test_log::log_cuda_device_properties(0, prop.name, prop.major, prop.minor,
                                         prop.totalGlobalMem, prop.canMapHostMemory);

    EXPECT_TRUE(prop.canMapHostMemory) << "GPU does not support host memory mapping";
}

TEST_F(CudaHostSystemTest, CudaHostAllocAndFree) {
    void* host_buffer = nullptr;
    size_t buffer_size = 64 * 1024;  // 64 KB

    // Allocate CUDA-pinned memory
    cuda_host_alloc(&host_buffer, buffer_size);

    DEBUG_LOG("Allocated CUDA-pinned buffer: %zu bytes at %p", buffer_size, host_buffer);

    // Write pattern to verify memory is accessible
    memset(host_buffer, 0xAB, buffer_size);
    EXPECT_EQ(((uint8_t*)host_buffer)[0], 0xAB);
    EXPECT_EQ(((uint8_t*)host_buffer)[buffer_size - 1], 0xAB);

    // Free
    cuda_host_free(host_buffer);
}

TEST_F(CudaHostSystemTest, CudaHostRegisterVfioBuffer) {
    HostPoolGuard pool(dev, config.num_buffers);
    ASSERT_TRUE(pool.valid());

    ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);

    cuda_host_register(buf->addr, buf->bytes);

    std::memset(buf->addr, 0xCD, buf->bytes);
    EXPECT_EQ(((uint8_t*)buf->addr)[0], 0xCD);

    cuda_host_unregister(buf->addr);
}

TEST_F(CudaHostSystemTest, NvmeReadToCudaBuffer) {
    const auto ctx = ioContext();
    HostPoolGuard pool(dev, 1);
    ASSERT_TRUE(pool.valid());

    ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);
    cuda_host_register(buf->addr, buf->bytes);

    nvme_test::clear_buffer(buf.get(), config.test_bytes);

    DEBUG_LOG("Submitting READ: NSID=%u, LBA=%lu, Size=%zu", config.nsid, config.slba, config.test_bytes);

    auto result = nvme_test::submit_read(
        ctx, buf.get(), config.slba, config.test_bytes, 5'000'000);

    EXPECT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
    EXPECT_TRUE(result.is_success()) << "NVMe read error";

    bool has_data = nvme_test::buffer_has_nonzero(buf.get(), config.test_bytes);
    DEBUG_LOG("Buffer contains data: %s", has_data ? "Yes" : "No (might be empty block)");

    cuda_host_unregister(buf->addr);
}

TEST_F(CudaHostSystemTest, NvmeWriteReadVerifyWithCuda) {
    const auto ctx = ioContext();
    HostPoolGuard pool(dev, 1);
    ASSERT_TRUE(pool.valid());

    ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);
    cuda_host_register(buf->addr, buf->bytes);

    nvme::patterns::DataPatterns::fill(buf->addr, config.test_bytes, nvme::patterns::PatternType::SEQUENTIAL, config.slba);
    auto write_result = nvme_test::submit_write(
        ctx, buf.get(), config.slba, config.test_bytes, 5'000'000);

    ASSERT_NE(write_result.submitted_cid, NVME_CID_QUEUE_FULL);
    EXPECT_TRUE(write_result.is_success());

    nvme_test::clear_buffer(buf.get(), config.test_bytes);

    auto read_result = nvme_test::submit_read(
        ctx, buf.get(), config.slba, config.test_bytes, 5'000'000);

    ASSERT_NE(read_result.submitted_cid, NVME_CID_QUEUE_FULL);
    EXPECT_TRUE(read_result.is_success());

    EXPECT_TRUE(nvme::patterns::DataPatterns::verify(
                    buf->addr, config.test_bytes,
                    nvme::patterns::PatternType::SEQUENTIAL, config.slba))
        << "Pattern verification failed";

    cuda_host_unregister(buf->addr);
}

TEST_F(CudaHostSystemTest, PerformanceCudaPinnedVsRegular) {
    const uint16_t num_iterations = 100;
    const auto ctx = ioContext();

    auto measure_reads = [&](HostPoolGuard& pool, bool register_cuda) -> std::chrono::microseconds {
        ScopedDmaBuf buf(pool);
        if (!buf.get()) {
            ADD_FAILURE() << "Failed to allocate buffer";
            return std::chrono::microseconds(0);
        }

        if (register_cuda) {
            cuda_host_register(buf->addr, buf->bytes);
        }

        auto start = std::chrono::high_resolution_clock::now();
        for (uint16_t i = 0; i < num_iterations; i++) {
            uint64_t slba = config.slba + (i % 1000);
            auto result = nvme_test::submit_read(
                ctx, buf.get(), slba, config.test_bytes, 5'000'000);
            if (result.submitted_cid == NVME_CID_QUEUE_FULL || !result.is_success()) {
                ADD_FAILURE() << "I/O operation failed at iteration " << i;
                break;
            }
        }
        auto end = std::chrono::high_resolution_clock::now();

        if (register_cuda) {
            cuda_host_unregister(buf->addr);
        }

        return std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    };

    HostPoolGuard regular_pool(dev, 1);
    ASSERT_TRUE(regular_pool.valid());
    auto duration_regular = measure_reads(regular_pool, false);

    HostPoolGuard cuda_pool(dev, 1);
    ASSERT_TRUE(cuda_pool.valid());
    auto duration_cuda = measure_reads(cuda_pool, true);

    test_log::calculate_and_log_performance_comparison(
        duration_regular.count(), duration_cuda.count(),
        num_iterations, config.test_bytes,
        "Regular Buffer", "CUDA-Pinned Buffer");
    printf("\n");
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    bool listing_only = ::testing::GTEST_FLAG(list_tests);

    printf("\n============================================================\n");
    printf("Module 54: CUDA Host Memory System Tests\n");
    printf("============================================================\n\n");

    if (!listing_only) {
        printf("Environment:\n");
        test_log::log_env_var("NVME_BDF", std::getenv("NVME_BDF"), "auto-detect");
        test_log::log_env_var("NVME_NSID", std::getenv("NVME_NSID"), "1");
        test_log::log_env_var("NVME_LBA_SIZE", std::getenv("NVME_LBA_SIZE"), "512");
        test_log::log_env_var("NVME_SLBA", std::getenv("NVME_SLBA"), "0");
        printf("\n");
    }

    int result = RUN_ALL_TESTS();

    printf("\n============================================================\n");
    printf("Module 54 CUDA Host Memory Tests Complete\n");
    printf("============================================================\n\n");

    return result;
}
