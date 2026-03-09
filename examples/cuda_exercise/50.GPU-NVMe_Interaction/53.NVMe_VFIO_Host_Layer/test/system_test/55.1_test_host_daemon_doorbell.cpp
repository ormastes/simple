/**
 * @file 55.1_test_host_daemon_doorbell.cpp
 * @brief Module 55.1 system tests using host queues with a doorbell daemon.
 */

// Enable debug logging for test actions
#define DEBUG_LOG_ENABLED 1

#include <chrono>
#include <gtest/gtest.h>

#include "common/forward_decls.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "doorbell/nvme_doorbell.h"

#include "doorbell/doorbell_daemon.h"
#include "helper/host_io_system_fixture.h"
#include "helper/log_helper.h"
#include "common/patterns/data_patterns.h"

using nvme_test::HostIoSystemTestBase;

/**
 * @brief Host doorbell daemon test fixture (Module 55.1)
 */
class HostDaemonDoorbellSystemTest : public HostIoSystemTestBase<DeferredDoorbell> {
protected:
    void add_custom_tasks(SetupHelper& helper) override {
        helper.add_task(new HostDoorbellDaemonTask(10));
    }

    void fetch_custom_handles() override {
        daemon_ = setup_helper()->get<nvme::DoorbellDaemon*>("host_doorbell_daemon");
        ASSERT_NE(daemon_, nullptr) << "HostDoorbellDaemonTask did not return a daemon handle";
    }

public:
    nvme::DoorbellDaemon* daemon() const { return daemon_; }

private:
    nvme::DoorbellDaemon* daemon_{nullptr};
};

DEFINE_HOST_IO_COMMON_TESTS(HostDaemonDoorbellSystemTest);
DEFINE_HOST_IO_PERF_TESTS(HostDaemonDoorbellSystemTest);

TEST_F(HostDaemonDoorbellSystemTest, HostDaemonRingsDoorbell) {
    nvme_test::HostPoolGuard pool(device(), 1);
    ASSERT_TRUE(pool.valid());

    nvme_test::ScopedDmaBuf buf(pool);
    ASSERT_NE(buf.get(), nullptr);
    nvme_test::clear_buffer(buf.get(), config().test_bytes);

    uint64_t previous_rings = daemon()->ring_count();
    auto result = submitRead(buf.get(), config().slba, config().test_bytes, 2'000'000);

    ASSERT_NE(result.submitted_cid, NVME_CID_QUEUE_FULL);
    ASSERT_TRUE(daemon()->wait_for_ring_count(previous_rings + 1, std::chrono::milliseconds(1000)))
        << "Host doorbell daemon did not ring within timeout";
    EXPECT_TRUE(result.is_success());
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    printf("\n=== Module 55.1 Host Daemon Doorbell System Tests ===\n");
    printf("Ensure NVME_BDF / NVME_NSID / NVME_LBA_SIZE / NVME_SLBA are set and VFIO is configured.\n\n");
    return RUN_ALL_TESTS();
}
