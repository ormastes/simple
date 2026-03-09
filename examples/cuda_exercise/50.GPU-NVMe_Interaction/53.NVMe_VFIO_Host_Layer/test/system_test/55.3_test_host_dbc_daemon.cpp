/**
 * @file 55.3_test_host_dbc_daemon.cpp
 * @brief Module 55.3 system tests for the host DBC daemon path.
 */

#include <unistd.h>
#include <gtest/gtest.h>

#include "common/forward_decls.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "doorbell/nvme_doorbell.h"

#include "helper/host_io_system_fixture.h"
#include "helper/log_helper.h"
#include "common/patterns/data_patterns.h"

using nvme_test::HostIoSystemTestBase;

/**
 * @brief Fixture enabling DBC shadow doorbells plus the host daemon.
 */
class HostDbcDaemonSystemTest : public HostIoSystemTestBase<EventIndexedDoorbell> {
protected:
    void add_custom_tasks(SetupHelper& helper) override {
        helper.add_task(new DbcShadowBufferTask(1, /*use_eventidx=*/false));
        helper.add_task(new HostDbcDaemonTask("standard", "/dev/nvme0", 1));
    }

    void fetch_custom_handles() override {
        daemon_handle_ = setup_helper()->get<void*>("host_dbc_daemon");
        shadow_buffer_ = setup_helper()->get<ShadowDoorbellBuffer*>("shadow_doorbell_buffer");
        ASSERT_NE(daemon_handle_, nullptr) << "HostDbcDaemonTask failed to launch daemon";
        ASSERT_NE(shadow_buffer_, nullptr) << "Shadow doorbell buffer not allocated";
    }

public:
    void* daemon_handle() const { return daemon_handle_; }
    ShadowDoorbellBuffer* shadow_buffer() const { return shadow_buffer_; }

private:
    void* daemon_handle_{nullptr};
    ShadowDoorbellBuffer* shadow_buffer_{nullptr};
};

DEFINE_HOST_IO_COMMON_TESTS(HostDbcDaemonSystemTest);
DEFINE_HOST_IO_PERF_TESTS(HostDbcDaemonSystemTest);

TEST_F(HostDbcDaemonSystemTest, DaemonSpawnsAndWritesShadowBuffer) {
    shadow_buffer()->host_ptr[0] = 5;
    shadow_buffer()->host_ptr[1] = 9;

    EXPECT_EQ(shadow_buffer()->host_ptr[0], 5u);
    EXPECT_EQ(shadow_buffer()->host_ptr[1], 9u);

    // Allow daemon time to observe updates.
    usleep(50'000);
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    printf("\n=== Module 55.3 Host DBC Daemon Tests ===\n");
    printf("Ensure NVIDIA GPU + NVMe hardware is configured before running.\n\n");
    return RUN_ALL_TESTS();
}
