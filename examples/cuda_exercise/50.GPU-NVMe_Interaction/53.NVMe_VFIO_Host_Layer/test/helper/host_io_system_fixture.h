/**
 * @file host_io_system_fixture.h
 * @brief Shared GTest fixture scaffolding for NVMe host I/O system tests
 */

#pragma once

#include <algorithm>
#include <chrono>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "device/device_detector.h"
#include "helper/host_io_test_utils.h"
#include "helper/log_helper.h"
#include "common/patterns/data_patterns.h"
#include "helper/setup_helper.h"
#include "helper/system_test_config.h"

namespace nvme_test {

/**
 * @brief Base fixture providing common NVMe device configuration for system tests
 *
 * @tparam DoorbellT Doorbell strategy used for host_submit operations
 */
template <typename DoorbellT>
class HostIoSystemTestBase : public ::testing::Test {
protected:
    HostTestConfig config_;
    std::unique_ptr<SetupHelper> setup_helper_;
    NvmeDevice* dev_{nullptr};
    Queue* iosq_{nullptr};
    Queue* iocq_{nullptr};
    SystemFeatures detected_features_;
    SelectedDevices selected_devices_;
    std::string skip_reason_;
    bool auto_config_attempted_{false};

    virtual void customize_config(HostTestConfig&) {}
    virtual void customize_global_args(SetupArgs&) {}
    virtual void add_custom_tasks(SetupHelper&) {}
    virtual void fetch_custom_handles() {}

    void SetUp() override {
        setup_helper_.reset();

        config_.load_from_env(nullptr, false);
        customize_config(config_);

        auto_config_attempted_ = true;
        std::string context = config_.is_valid()
            ? "Validating provided NVME_BDF. "
            : "NVME_BDF not provided. ";

        CHECK_SKIP_CLEANUP(
            select_test_devices(detected_features_, selected_devices_, skip_reason_, config_.bdf),
            {
                skip_reason_ = context + skip_reason_;
                setup_helper_.reset();
            },
            skip_reason_
        );

        config_.load_from_env(&selected_devices_);

        setup_helper_ = std::make_unique<SetupHelper>();
        SetupArgs args = config_.get_setup_args();
        customize_global_args(args);
        setup_helper_->set_global_args(args);
        setup_helper_->add_task(new NvmeSetupTask());
        setup_helper_->add_task(new HostMemoryFactoryTask(config_.test_bytes, config_.num_buffers));
        add_custom_tasks(*setup_helper_);

        CHECK_SKIP_CLEANUP(
            setup_helper_->setup_all(),
            setup_helper_.reset(),
            "SetupHelper failed to configure NVMe device."
        );

        CHECK_SKIP_CLEANUP(
            (dev_ = setup_helper_->get<NvmeDevice*>("nvme_device")) != nullptr,
            setup_helper_.reset(),
            "SetupHelper did not return nvme_device handle."
        );

        iosq_ = nvme_get_iosq(dev_);
        iocq_ = nvme_get_iocq(dev_);
        fetch_custom_handles();
    }

    void TearDown() override {
        iosq_ = nullptr;
        iocq_ = nullptr;
        dev_ = nullptr;
        setup_helper_.reset();
    }

    IoContext ioContext() const {
        return IoContext{dev_, iosq_, iocq_, &config_};
    }

    IoCompletion submitRead(DmaBuf* buf, uint64_t slba, size_t bytes,
                            uint64_t timeout_us = 5'000'000) const {
        return nvme_test::submit_read<DoorbellT>(ioContext(), buf, slba, bytes, timeout_us);
    }

    IoCompletion submitWrite(DmaBuf* buf, uint64_t slba, size_t bytes,
                             uint64_t timeout_us = 5'000'000) const {
        return nvme_test::submit_write<DoorbellT>(ioContext(), buf, slba, bytes, timeout_us);
    }

    template<typename CustomDoorbellT>
    IoCompletion submitReadWith(DmaBuf* buf, uint64_t slba, size_t bytes,
                                uint64_t timeout_us = 5'000'000) const {
        return nvme_test::submit_read<CustomDoorbellT>(ioContext(), buf, slba, bytes, timeout_us);
    }

    template<typename CustomDoorbellT>
    IoCompletion submitWriteWith(DmaBuf* buf, uint64_t slba, size_t bytes,
                                 uint64_t timeout_us = 5'000'000) const {
        return nvme_test::submit_write<CustomDoorbellT>(ioContext(), buf, slba, bytes, timeout_us);
    }

public:
    const HostTestConfig& config() const { return config_; }
    NvmeDevice* device() const { return dev_; }
    Queue* submission_queue() const { return iosq_; }
    Queue* completion_queue() const { return iocq_; }
    SetupHelper* setup_helper() const { return setup_helper_.get(); }
};

}  // namespace nvme_test

// -----------------------------------------------------------------------------
// Common test definitions
// -----------------------------------------------------------------------------

#define DEFINE_HOST_IO_COMMON_TESTS(FixtureClass) \
TEST_F(FixtureClass, DeviceInitialization) { \
    auto* dev = this->device(); \
    uint32_t page_size = nvme_get_page_size(dev); \
    uint32_t max_page_size = nvme_get_max_page_size(dev); \
    uint32_t lba_size = nvme_get_lba_size(dev); \
    ItemSize item_size = nvme_get_item_size(dev); \
    test_log::log_device_properties(page_size, max_page_size, lba_size, \
                                     item_size.total_size, item_size.lba_count); \
} \
\
TEST_F(FixtureClass, PoolCreationAndManagement) { \
    nvme_test::HostPoolGuard pool(this->device(), this->config().num_buffers); \
    ASSERT_TRUE(pool.valid()) << "Failed to create host pool"; \
    test_log::log_pool_properties(pool.capacity(), pool.buffer_size(), pool.in_use()); \
    auto buffers = nvme_test::acquire_buffers(pool, this->config().num_buffers); \
    EXPECT_EQ(buffers.size(), this->config().num_buffers); \
    nvme_test::release_buffers(pool, buffers); \
} \
\
TEST_F(FixtureClass, SingleBlockRead) { \
    nvme_test::HostPoolGuard pool(this->device(), 2); \
    ASSERT_TRUE(pool.valid()); \
    nvme_test::ScopedDmaBuf buf(pool); \
    ASSERT_NE(buf.get(), nullptr); \
    nvme_test::clear_buffer(buf.get(), this->config().test_bytes); \
    test_log::log_io_submission("READ", this->config().nsid, this->config().slba, \
                                 this->config().test_bytes, buf->addr, buf->iova); \
    test_log::log_queue_details(this->submission_queue()->vaddr, \
                                (void*)this->submission_queue()->db, \
                                (void*)this->submission_queue()->read_cmd_pool, \
                                (void*)this->submission_queue()->write_cmd_pool); \
    auto result = this->submitRead(buf.get(), this->config().slba, this->config().test_bytes, 1'000'000); \
    EXPECT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
    EXPECT_TRUE(result.is_success()) << "NVMe read failed"; \
} \
\
TEST_F(FixtureClass, WriteReadVerifySequential) { \
    nvme_test::HostPoolGuard pool(this->device(), 2); \
    ASSERT_TRUE(pool.valid()); \
    { \
        nvme_test::ScopedDmaBuf write_buf(pool); \
        ASSERT_NE(write_buf.get(), nullptr); \
        nvme::patterns::DataPatterns::fill(write_buf->addr, this->config().test_bytes, nvme::patterns::PatternType::SEQUENTIAL, this->config().slba); \
        auto write_result = this->submitWrite(write_buf.get(), this->config().slba, this->config().test_bytes); \
        ASSERT_NE(write_result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(write_result.is_success()) << "NVMe write failed"; \
    } \
    { \
        nvme_test::ScopedDmaBuf read_buf(pool); \
        ASSERT_NE(read_buf.get(), nullptr); \
        nvme_test::clear_buffer(read_buf.get(), this->config().test_bytes); \
        auto read_result = this->submitRead(read_buf.get(), this->config().slba, this->config().test_bytes); \
        ASSERT_NE(read_result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(read_result.is_success()) << "NVMe read failed"; \
    EXPECT_TRUE(nvme::patterns::DataPatterns::verify(read_buf->addr, this->config().test_bytes, nvme::patterns::PatternType::SEQUENTIAL, this->config().slba)) \
        << "Pattern verification failed"; \
} \
} \
\
TEST_F(FixtureClass, MultipleOutstandingCommands) { \
    const uint16_t num_cmds = 4; \
    nvme_test::HostPoolGuard pool(this->device(), num_cmds); \
    ASSERT_TRUE(pool.valid()); \
    std::vector<uint16_t> cids; \
    std::vector<DmaBuf*> buffers; \
    buffers.reserve(num_cmds); \
    for (uint16_t i = 0; i < num_cmds; i++) { \
        DmaBuf* buf = pool.acquire(); \
        ASSERT_NE(buf, nullptr); \
        buffers.push_back(buf); \
        nvme_test::clear_buffer(buf, this->config().test_bytes); \
        uint64_t slba = this->config().slba + (i * 8); \
        auto result = this->submitRead(buf, slba, this->config().test_bytes); \
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        cids.push_back(result.submitted_cid); \
    } \
    std::vector<uint16_t> completed_cids; \
    for (uint16_t i = 0; i < num_cmds; i++) { \
        uint16_t cid = 0; \
        NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(this->completion_queue(), &cid, nullptr, 0, this->submission_queue()); \
        (void)status; \
        completed_cids.push_back(cid); \
    } \
    std::sort(cids.begin(), cids.end()); \
    std::sort(completed_cids.begin(), completed_cids.end()); \
    EXPECT_EQ(cids, completed_cids) << "Not all commands completed"; \
    for (auto* buf : buffers) { \
        pool.release(buf); \
    } \
} \
\
TEST_F(FixtureClass, ErrorHandlingInvalidSLBA) { \
    nvme_test::HostPoolGuard pool(this->device(), 1); \
    ASSERT_TRUE(pool.valid()); \
    nvme_test::ScopedDmaBuf buf(pool); \
    ASSERT_NE(buf.get(), nullptr); \
    uint64_t invalid_slba = 0xFFFFFFFFFFFFFFFFULL - 100; \
    auto result = this->submitRead(buf.get(), invalid_slba, this->config().test_bytes); \
    if (result.submitted_cid != NVME_CID_QUEUE_FULL) { \
        EXPECT_TRUE(result.status.is_error()) << "Expected completion error for invalid SLBA"; \
        if (result.status.is_error()) { \
            test_log::log_nvme_error(result.status.sct, result.status.sc, result.status.dnr); \
        } \
    } \
}

#define DEFINE_HOST_IO_PERF_TESTS(FixtureClass) \
TEST_F(FixtureClass, PerformanceSequentialRead) { \
    const uint16_t num_iterations = 1000; \
    const size_t io_size = this->config().test_bytes; \
    nvme_test::HostPoolGuard pool(this->device(), this->config().num_buffers); \
    ASSERT_TRUE(pool.valid()); \
    auto bufs = nvme_test::acquire_buffers(pool, this->config().num_buffers); \
    ASSERT_FALSE(bufs.empty()); \
    test_log::log_benchmark_config(num_iterations, io_size); \
    for (int i = 0; i < 10; ++i) { \
        DmaBuf* buf = bufs[i % bufs.size()]; \
        auto result = this->submitRead(buf, this->config().slba + i, io_size, 5'000'000); \
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(result.is_success()); \
    } \
    auto start = std::chrono::high_resolution_clock::now(); \
    for (uint16_t i = 0; i < num_iterations; ++i) { \
        DmaBuf* buf = bufs[i % bufs.size()]; \
        uint64_t lba = this->config().slba + (i * 8) % 10000; \
        auto result = this->submitRead(buf, lba, io_size, 5'000'000); \
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(result.is_success()); \
    } \
    auto end = std::chrono::high_resolution_clock::now(); \
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start); \
    test_log::calculate_and_log_performance(duration.count(), num_iterations, io_size); \
    nvme_test::release_buffers(pool, bufs); \
} \
\
TEST_F(FixtureClass, PerformanceSequentialWrite) { \
    const uint16_t num_iterations = 1000; \
    const size_t io_size = this->config().test_bytes; \
    nvme_test::HostPoolGuard pool(this->device(), this->config().num_buffers); \
    ASSERT_TRUE(pool.valid()); \
    auto bufs = nvme_test::acquire_buffers(pool, this->config().num_buffers); \
    ASSERT_FALSE(bufs.empty()); \
    for (auto* buf : bufs) { \
        std::memset(buf->addr, 0xAB, io_size); \
    } \
    test_log::log_benchmark_config(num_iterations, io_size); \
    auto start = std::chrono::high_resolution_clock::now(); \
    for (uint16_t i = 0; i < num_iterations; ++i) { \
        DmaBuf* buf = bufs[i % bufs.size()]; \
        uint64_t lba = this->config().slba + (i * 8) % 10000; \
        auto result = this->submitWrite(buf, lba, io_size, 5'000'000); \
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(result.is_success()); \
    } \
    auto end = std::chrono::high_resolution_clock::now(); \
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start); \
    test_log::calculate_and_log_performance(duration.count(), num_iterations, io_size); \
    nvme_test::release_buffers(pool, bufs); \
} \
\
TEST_F(FixtureClass, PerformanceLatencyDistribution) { \
    const uint16_t num_samples = 500; \
    const size_t io_size = this->config().test_bytes; \
    nvme_test::HostPoolGuard pool(this->device(), 1); \
    ASSERT_TRUE(pool.valid()); \
    nvme_test::ScopedDmaBuf buf(pool); \
    ASSERT_NE(buf.get(), nullptr); \
    std::vector<double> latencies; \
    latencies.reserve(num_samples); \
    for (uint16_t i = 0; i < num_samples; ++i) { \
        uint64_t lba = this->config().slba + (i % 1000); \
        auto start = std::chrono::high_resolution_clock::now(); \
        auto result = this->submitRead(buf.get(), lba, io_size, 5'000'000); \
        auto end = std::chrono::high_resolution_clock::now(); \
        ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        EXPECT_TRUE(result.is_success()); \
        double latency_us = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() / 1000.0; \
        latencies.push_back(latency_us); \
    } \
    test_log::calculate_and_log_latency_stats(latencies); \
} \
\
TEST_F(FixtureClass, PerformanceQueueDepthScaling) { \
    const uint16_t max_qd = std::min(this->config().sq_depth, static_cast<uint16_t>(8)); \
    const uint16_t ops_per_qd = 200; \
    const size_t io_size = this->config().test_bytes; \
    nvme_test::HostPoolGuard pool(this->device(), max_qd); \
    ASSERT_TRUE(pool.valid()); \
    auto bufs = nvme_test::acquire_buffers(pool, max_qd); \
    ASSERT_EQ(bufs.size(), max_qd); \
    for (uint16_t qd = 1; qd <= max_qd; ++qd) { \
        uint16_t total_ops = qd * ops_per_qd; \
        uint16_t ops_submitted = 0; \
        uint16_t ops_completed = 0; \
        auto start = std::chrono::high_resolution_clock::now(); \
        for (uint16_t i = 0; i < qd && ops_submitted < total_ops; ++i, ++ops_submitted) { \
            DmaBuf* buf = bufs[i % qd]; \
            uint64_t lba = this->config().slba + (ops_submitted % 1000); \
            auto result = this->submitRead(buf, lba, io_size, 5'000'000); \
            ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
        } \
        while (ops_completed < total_ops) { \
            uint16_t cid = 0; \
            PollResult poll_result = POLL_TIMEOUT; \
            NvmeStatus status = host_poll_completion<ASYNC_TYPE_SYNC>(this->completion_queue(), &cid, &poll_result, 5'000'000, this->submission_queue()); \
            (void)status; \
            ++ops_completed; \
            if (ops_submitted < total_ops) { \
                DmaBuf* buf = bufs[ops_submitted % qd]; \
                uint64_t lba = this->config().slba + (ops_submitted % 1000); \
                auto result = this->submitRead(buf, lba, io_size, 5'000'000); \
                ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL); \
                ++ops_submitted; \
            } \
        } \
        auto end = std::chrono::high_resolution_clock::now(); \
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start); \
        test_log::calculate_and_log_qd_result(duration.count(), qd, total_ops, io_size); \
    } \
    nvme_test::release_buffers(pool, bufs); \
}
