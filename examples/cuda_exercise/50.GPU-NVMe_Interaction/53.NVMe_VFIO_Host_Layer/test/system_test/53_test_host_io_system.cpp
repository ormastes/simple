/**
 * @file test_host_io_system.cpp
 * @brief Combined system tests for Module 53 host I/O paths (MMIO + SetupHelper)
 *
 * This file merges the original MMIO-focused system test with the SetupHelper
 * variant so that all Module 53 system coverage lives in one translation unit.
 * Tests exercise:
 * - Host I/O queue setup (submission and completion)
 * - MMIO doorbell operations
 * - Host buffer pool creation and DMA mapping
 * - NVMe command submission and completion polling
 * - SetupHelper task graph flows with automatic cleanup
 * - Pattern generation/verification for integrity checks
 *
 * Requirements:
 * - Real NVMe device accessible via VFIO
 * - Environment variables:
 *   - NVME_BDF: PCI Bus:Device.Function (e.g., "0000:41:00.0")
 *   - NVME_NSID: Namespace ID (typically "1")
 *   - NVME_LBA_SIZE: Logical block size ("512" or "4096")
 *   - NVME_SLBA: Starting LBA for test area (must be safe to overwrite)
 */

// Enable debug logging for test actions
#define DEBUG_LOG_ENABLED 1

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <unistd.h>
#include <vector>

#include <gtest/gtest.h>
#include "cuda_utils.h"  // For DEBUG_LOG

// Module 53 APIs
#include "common/forward_decls.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "doorbell/nvme_doorbell.h"
#include "common/patterns/data_patterns.h"
#include "helper/host_io_test_utils.h"

#include "device/device_detector.h"
#include "device/device_detector.h"
#include "helper/setup_helper.h"
#include "helper/vfio_utils.h"

// Test helpers
#include "helper/system_test_config.h"
#include "helper/log_helper.h"

// Bring in test config types
using nvme_test::HostTestConfig;
using nvme_test::INVALID_PCI_BUS_ID;
using nvme_test::select_test_devices;
using nvme_test::HostPoolGuard;
using nvme_test::IoContext;
using nvme_test::IoCompletion;
using nvme_test::ScopedDmaBuf;

/**
 * @brief System test fixture for host I/O with MMIO doorbell
 *
 * Provides automatic device initialization/cleanup and test infrastructure.
 */
class HostIoMmioSystemTest : public ::testing::Test {
protected:
    HostTestConfig config;
    NvmeDevice* dev{nullptr};
    Queue* iosq{nullptr};
    Queue* iocq{nullptr};
    SystemFeatures detected_features_;
    SelectedDevices selected_devices_;
    bool auto_config_attempted_{false};
    std::string skip_reason_;
    std::unique_ptr<SetupHelper> setup_helper_;

    void SetUp() override {
        setup_helper_.reset();

        // Try loading from environment first
        config.load_from_env(nullptr, false);  // Don't log yet

        // Auto-configure with optional BDF (validates and selects device)
        auto_config_attempted_ = true;
        std::string context = config.is_valid()
            ? "Validating provided NVME_BDF. "
            : "NVME_BDF not provided. ";

        CHECK_SKIP_CLEANUP(
            select_test_devices(detected_features_, selected_devices_, skip_reason_, config.bdf),
            { skip_reason_ = context + skip_reason_; setup_helper_.reset(); },
            skip_reason_
        );

        // Load config from selected device (or environment if BDF was valid)
        config.load_from_env(&selected_devices_);

        // Initialize SetupHelper with config
        setup_helper_ = std::make_unique<SetupHelper>();
        setup_helper_->set_global_args(config.get_setup_args());
        setup_helper_->add_task(new NvmeSetupTask());  // Handles VFIO binding internally

        CHECK_SKIP_CLEANUP(
            setup_helper_->setup_all(),
            setup_helper_.reset(),
            skip_reason_ + "SetupHelper failed to configure NVMe device. Check stderr for details."
        );

        CHECK_SKIP_CLEANUP(
            (dev = setup_helper_->get<NvmeDevice*>("nvme_device")) != nullptr,
            setup_helper_.reset(),
            "SetupHelper did not return nvme_device handle."
        );

        // Get Queue pointers from device (needed for host_submit)
        iosq = nvme_get_iosq(dev);
        iocq = nvme_get_iocq(dev);
        DEBUG_LOG("Device initialized via SetupHelper: SQ=%p CQ=%p (depth=%u/%u)",
                  iosq, iocq, config.sq_depth, config.cq_depth);
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
// Test 1: Basic Device Initialization
// ============================================================================

TEST_F(HostIoMmioSystemTest, DeviceInitialization) {
    // Log device properties
    uint32_t page_size = nvme_get_page_size(dev);
    uint32_t max_page_size = nvme_get_max_page_size(dev);
    uint32_t lba_size = nvme_get_lba_size(dev);
    ItemSize item_size = nvme_get_item_size(dev);

    test_log::log_device_properties(page_size, max_page_size, lba_size,
                                     item_size.total_size, item_size.lba_count);
}

// ============================================================================
// Test 2: Page Size Configuration Query (demonstrates README example)
// ============================================================================

TEST_F(HostIoMmioSystemTest, PageSizeConfigurationQuery) {
    // This test demonstrates the page size query functionality as shown in README.md
    // Note: SetupHelper already initialized the device, so we demonstrate query functions
    
    // Query available page sizes (as shown in README example)
    size_t num_sizes;
    size_t* available = nvme_available_sizes(dev, &num_sizes);
    ASSERT_NE(available, nullptr) << "nvme_available_sizes() should not return nullptr";
    ASSERT_GT(num_sizes, 0) << "Device should support at least one page size";

    printf("Supported page sizes: ");
    for (size_t i = 0; i < num_sizes; i++) {
        printf("%zuKB ", available[i] / 1024);
    }
    printf("\n");

    // Verify current page size is in the available list
    size_t current_page_size = nvme_get_page_size(dev);
    bool current_found = false;
    for (size_t i = 0; i < num_sizes; i++) {
        if (available[i] == current_page_size) {
            current_found = true;
            break;
        }
    }
    EXPECT_TRUE(current_found) 
        << "Current page size " << current_page_size << " should be in available sizes";

    printf("Current page size: %zu bytes (%zuKB)\n", 
           current_page_size, current_page_size / 1024);

    free(available);
    
    // Note: nvme_set_page_size() must be called before controller enablement,
    // so it's not demonstrated here as SetupHelper already initialized the device.
    // See test_page_size_config_system for comprehensive configuration testing.
}

// ============================================================================
// Test 3: Pool Creation and Management
// ============================================================================

TEST_F(HostIoMmioSystemTest, PoolCreationAndManagement) {
    HostPoolGuard pool(dev, config.num_buffers);
    ASSERT_TRUE(pool.valid()) << "Failed to create host pool";

    test_log::log_pool_properties(pool.capacity(), pool.buffer_size(), pool.in_use());

    auto buffers = nvme_test::acquire_buffers(pool, config.num_buffers);
    EXPECT_EQ(buffers.size(), config.num_buffers);
    nvme_test::release_buffers(pool, buffers);
}

// ============================================================================
// Test 4: Single Block Read Operation
// ============================================================================

TEST_F(HostIoMmioSystemTest, SingleBlockRead) {

    const auto ctx = ioContext();
    HostPoolGuard pool(dev, 2);
    ASSERT_TRUE(pool.valid());

    ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);
    nvme_test::clear_buffer(buf.get(), config.test_bytes);

    test_log::log_io_submission("READ", config.nsid, config.slba, config.test_bytes,
                                buf->addr, buf->iova);
    test_log::log_queue_details(iosq->vaddr, (void*)iosq->db,
                                (void*)iosq->read_cmd_pool, (void*)iosq->write_cmd_pool);

    auto result = nvme_test::submit_read(ctx, buf.get(), config.slba, config.test_bytes, 1'000'000);

    EXPECT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
    EXPECT_TRUE(result.is_success()) << "NVMe read failed";

}

// ============================================================================
// Test 5: Write-Read-Verify with Sequential Pattern
// ============================================================================

TEST_F(HostIoMmioSystemTest, WriteReadVerifySequential) {

    const auto ctx = ioContext();
    HostPoolGuard pool(dev, 2);
    ASSERT_TRUE(pool.valid());

    {
        ScopedDmaBuf write_buf(pool);
        ASSERT_NE(write_buf.get(), nullptr);
        nvme::patterns::DataPatterns::fill(write_buf->addr, config.test_bytes,
                                           nvme::patterns::PatternType::SEQUENTIAL, config.slba);

        auto write_result = nvme_test::submit_write(
            ctx, write_buf.get(), config.slba, config.test_bytes);

        ASSERT_NE(write_result.submitted_cid, NVME_CID_QUEUE_FULL);
        EXPECT_TRUE(write_result.is_success()) << "NVMe write failed";
    }

    {
        ScopedDmaBuf read_buf(pool);
        ASSERT_NE(read_buf.get(), nullptr);
        nvme_test::clear_buffer(read_buf.get(), config.test_bytes);

        auto read_result = nvme_test::submit_read(
            ctx, read_buf.get(), config.slba, config.test_bytes);

        ASSERT_NE(read_result.submitted_cid, NVME_CID_QUEUE_FULL);
        EXPECT_TRUE(read_result.is_success()) << "NVMe read failed";

        EXPECT_TRUE(nvme::patterns::DataPatterns::verify(
                        read_buf->addr, config.test_bytes,
                        nvme::patterns::PatternType::SEQUENTIAL, config.slba))
            << "Pattern verification failed";
    }

}

// ============================================================================
// Test 6: Multiple Outstanding Commands (Queue Depth Test)
// ============================================================================

TEST_F(HostIoMmioSystemTest, MultipleOutstandingCommands) {

    const uint16_t num_cmds = 4;
    const auto ctx = ioContext();
    HostPoolGuard pool(dev, num_cmds);
    ASSERT_TRUE(pool.valid());

    std::vector<uint16_t> cids;
    std::vector<DmaBuf*> buffers;
    buffers.reserve(num_cmds);

    // Submit multiple read commands
    for (uint16_t i = 0; i < num_cmds; i++) {
        DmaBuf* buf = pool.acquire();
        ASSERT_NE(buf, nullptr);
        buffers.push_back(buf);

        nvme_test::clear_buffer(buf, config.test_bytes);

        uint64_t slba = config.slba + (i * 8);  // Each command reads 8 blocks apart
        auto result = nvme_test::submit_read(ctx, buf, slba, config.test_bytes);
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
        cids.push_back(result.submitted_cid);

    }

    // Poll for all completions
    std::vector<uint16_t> completed_cids;

    for (uint16_t i = 0; i < num_cmds; i++) {
        uint16_t cid = 0;
        NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &cid, nullptr, 0, iosq);
        (void)status;
        completed_cids.push_back(cid);
    }

    // Verify all commands completed (order may differ)
    std::sort(cids.begin(), cids.end());
    std::sort(completed_cids.begin(), completed_cids.end());
    EXPECT_EQ(cids, completed_cids) << "Not all commands completed";


    // Cleanup
    for (auto* buf : buffers) {
        pool.release(buf);
    }

}

// ============================================================================
// Test 7: Error Handling - Invalid SLBA
// ============================================================================

TEST_F(HostIoMmioSystemTest, ErrorHandlingInvalidSLBA) {
    const auto ctx = ioContext();
    HostPoolGuard pool(dev, 1);
    ASSERT_TRUE(pool.valid());

    ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);

    uint64_t invalid_slba = 0xFFFFFFFFFFFFFFFFULL - 100;
    auto result = nvme_test::submit_read(ctx, buf.get(), invalid_slba, config.test_bytes);

    if (result.submitted_cid != NVME_CID_QUEUE_FULL) {
        EXPECT_TRUE(result.status.is_error()) << "Expected completion error for invalid SLBA";
        if (result.status.is_error()) {
            test_log::log_nvme_error(result.status.sct, result.status.sc, result.status.dnr);
        }
    }

}

// ============================================================================
// Performance Benchmarking Tests
// ============================================================================

TEST_F(HostIoMmioSystemTest, PerformanceSequentialRead) {

    const uint16_t num_iterations = 1000;  // Number of read operations
    const size_t io_size = config.test_bytes;  // 4096 bytes (8 LBAs)
    const auto ctx = ioContext();

    HostPoolGuard pool(dev, config.num_buffers);
    ASSERT_TRUE(pool.valid());
    auto bufs = nvme_test::acquire_buffers(pool, config.num_buffers);
    ASSERT_FALSE(bufs.empty());

    test_log::log_benchmark_config(num_iterations, io_size);

    for (int i = 0; i < 10; i++) {
        DmaBuf* buf = bufs[i % bufs.size()];
        auto result = nvme_test::submit_read(
            ctx, buf, config.slba + i, io_size, 5'000'000);
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
        EXPECT_TRUE(result.is_success());
    }

    // Benchmark phase
    auto start = std::chrono::high_resolution_clock::now();

    for (uint16_t i = 0; i < num_iterations; i++) {
        DmaBuf* buf = bufs[i % bufs.size()];
        uint64_t lba = config.slba + (i * 8) % 10000;  // Sequential within 10000 LBA range

        auto result = nvme_test::submit_read(
            ctx, buf, lba, io_size, 5'000'000);
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
        EXPECT_TRUE(result.is_success());
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    // Calculate and log metrics
    test_log::calculate_and_log_performance(duration.count(), num_iterations, io_size);

    // Cleanup
    nvme_test::release_buffers(pool, bufs);

}

TEST_F(HostIoMmioSystemTest, PerformanceSequentialWrite) {

    const uint16_t num_iterations = 1000;
    const size_t io_size = config.test_bytes;

    HostPool* pool = host_pool_create(dev, config.num_buffers);

    std::vector<DmaBuf*> bufs;
    for (int i = 0; i < config.num_buffers; i++) {
        DmaBuf* buf = host_pool_acquire(pool);
        // Fill with test pattern
        std::memset(buf->addr, 0xAA, io_size);
        bufs.push_back(buf);
    }

    test_log::log_benchmark_config(num_iterations, io_size);

    // Warm-up
    for (int i = 0; i < 10; i++) {
        DmaBuf* buf = bufs[i % bufs.size()];
        uint16_t cid = host_submit<CMD_WRITE, DOORBELL_MMIO>(
            iosq, config.nsid, config.slba + i, config.lba_size, buf, io_size);
        uint16_t completed_cid = 0;
        PollResult poll_result;
        NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 5000000, iosq);  // 5s timeout
    }

    // Benchmark
    auto start = std::chrono::high_resolution_clock::now();

    for (uint16_t i = 0; i < num_iterations; i++) {
        DmaBuf* buf = bufs[i % bufs.size()];
        uint64_t lba = config.slba + (i * 8) % 10000;

        uint16_t cid = host_submit<CMD_WRITE, DOORBELL_MMIO>(
            iosq, config.nsid, lba, config.lba_size, buf, io_size);

        uint16_t completed_cid = 0;
        PollResult poll_result;
        NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 5000000, iosq);  // 5s timeout
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    test_log::calculate_and_log_performance(duration.count(), num_iterations, io_size);

    for (auto* buf : bufs) {
        host_pool_release(pool, buf);
    }
    host_pool_destroy(pool);

}

TEST_F(HostIoMmioSystemTest, PerformanceLatencyDistribution) {

    const uint16_t num_samples = 1000;
    const size_t io_size = config.test_bytes;

    HostPool* pool = host_pool_create(dev, 1);

    DmaBuf* buf = host_pool_acquire(pool);

    std::vector<double> latencies;
    latencies.reserve(num_samples);


    for (uint16_t i = 0; i < num_samples; i++) {
        uint64_t lba = config.slba + (i % 1000);

        auto start = std::chrono::high_resolution_clock::now();

        uint16_t cid = host_submit<CMD_READ, DOORBELL_MMIO>(
            iosq, config.nsid, lba, config.lba_size, buf, io_size);

        uint16_t completed_cid = 0;
        PollResult poll_result;
        NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 5000000, iosq);  // 5s timeout

        auto end = std::chrono::high_resolution_clock::now();


        double latency_us = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() / 1000.0;
        latencies.push_back(latency_us);
    }

    
    test_log::calculate_and_log_latency_stats(latencies);
    

    host_pool_release(pool, buf);
    host_pool_destroy(pool);

}

TEST_F(HostIoMmioSystemTest, PerformanceQueueDepthScaling) {

    const uint16_t max_qd = std::min(config.sq_depth, (uint16_t)8);  // Test up to QD=8
    const uint16_t ops_per_qd = 500;
    const size_t io_size = config.test_bytes;

    HostPool* pool = host_pool_create(dev, max_qd);

    std::vector<DmaBuf*> bufs;
    for (int i = 0; i < max_qd; i++) {
        DmaBuf* buf = host_pool_acquire(pool);
        bufs.push_back(buf);
    }


    for (uint16_t qd = 1; qd <= max_qd; qd++) {
        uint16_t total_ops = qd * ops_per_qd;
        uint16_t ops_completed = 0;
        uint16_t ops_submitted = 0;

        auto start = std::chrono::high_resolution_clock::now();

        // Submit initial batch
        for (uint16_t i = 0; i < qd && ops_submitted < total_ops; i++, ops_submitted++) {
            DmaBuf* buf = bufs[i % qd];
            uint64_t lba = config.slba + (ops_submitted % 1000);
            uint16_t cid = host_submit<CMD_READ, DOORBELL_MMIO>(
                iosq, config.nsid, lba, config.lba_size, buf, io_size);
        }

        // Pipeline: complete one, submit one
        while (ops_completed < total_ops) {
            uint16_t completed_cid = 0;
            PollResult poll_result;
            NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 5000000, iosq);  // 5s timeout
            ops_completed++;

            // Submit next operation
            if (ops_submitted < total_ops) {
                DmaBuf* buf = bufs[ops_submitted % qd];
                uint64_t lba = config.slba + (ops_submitted % 1000);
                uint16_t cid = host_submit<CMD_READ, DOORBELL_MMIO>(
                    iosq, config.nsid, lba, config.lba_size, buf, io_size);
                ops_submitted++;
            }
        }

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

        test_log::calculate_and_log_qd_result(duration.count(), qd, total_ops, io_size);
    }

    

    for (auto* buf : bufs) {
        host_pool_release(pool, buf);
    }
    host_pool_destroy(pool);

}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    bool listing_only = ::testing::GTEST_FLAG(list_tests);

    printf("\n============================================================\n");
    printf("Module 53: Host I/O System Tests (MMIO + SetupHelper)\n");
    printf("============================================================\n\n");

    if (!listing_only) {
        printf("Environment:\n");
        test_log::log_env_var("NVME_BDF", std::getenv("NVME_BDF"), "auto-detect");
        test_log::log_env_var("NVME_NSID", std::getenv("NVME_NSID"), "1");
        test_log::log_env_var("NVME_LBA_SIZE", std::getenv("NVME_LBA_SIZE"), "512");
        test_log::log_env_var("NVME_SLBA", std::getenv("NVME_SLBA"), "0");
        
    }

    int result = RUN_ALL_TESTS();

    printf("\n============================================================\n");
    printf("Module 53 Host I/O System Tests Complete\n");
    printf("============================================================\n\n");

    return result;
}
