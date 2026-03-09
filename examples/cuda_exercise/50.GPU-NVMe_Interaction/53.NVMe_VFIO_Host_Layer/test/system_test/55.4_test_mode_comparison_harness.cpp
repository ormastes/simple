/**
 * @file 55.4_test_mode_comparison_harness.cpp
 * @brief Module 55.4 system tests comparing multiple doorbell/queue modes.
 */

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
 * @brief Harness fixture running baseline host-MMIO tests.
 */
class ModeComparisonHarnessTest : public HostIoSystemTestBase<ImmediateDoorbell> {
protected:
    void add_custom_tasks(SetupHelper&) override {}
};

DEFINE_HOST_IO_COMMON_TESTS(ModeComparisonHarnessTest);
DEFINE_HOST_IO_PERF_TESTS(ModeComparisonHarnessTest);

TEST_F(ModeComparisonHarnessTest, ConfigureDoorbellModes) {
    auto run_mode = [&](const char* name, auto config_fn) {
        printf("\n=== Configuring mode: %s ===\n", name);
        SetupHelper helper;
        helper.set_global_args(config().get_setup_args());
        helper.add_task(new NvmeSetupTask());
        helper.add_task(new HostMemoryFactoryTask(config().test_bytes, config().num_buffers));
        config_fn(helper);
        ASSERT_TRUE(helper.setup_all());
    };

    run_mode("host_mmio", [&](SetupHelper&) {
        // Already covered by default tasks
    });

    run_mode("host_daemon", [&](SetupHelper& helper) {
        helper.add_task(new HostDoorbellDaemonTask(10));
    });

    run_mode("shadow_doorbell", [&](SetupHelper& helper) {
        helper.add_task(new DbcShadowBufferTask(1, false));
    });

    run_mode("host_dbc_daemon", [&](SetupHelper& helper) {
        helper.add_task(new DbcShadowBufferTask(1, false));
        helper.add_task(new HostDbcDaemonTask("standard", "/dev/nvme0", 1));
    });
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    printf("\n=== Module 55.4 Mode Comparison Harness ===\n");
    printf("Scaffolding for comparing multiple doorbell/queue modes.\n\n");
    return RUN_ALL_TESTS();
}
