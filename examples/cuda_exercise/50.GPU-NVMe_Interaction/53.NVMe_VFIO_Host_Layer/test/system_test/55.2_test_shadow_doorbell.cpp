/**
 * @file 55.2_test_shadow_doorbell.cpp
 * @brief Module 55.2 system tests for doorbell buffer configuration (DBC shadow doorbells).
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
 * @brief Shadow doorbell test fixture using event-indexed doorbells.
 */
class ShadowDoorbellSystemTest : public HostIoSystemTestBase<EventIndexedDoorbell> {
protected:
    void add_custom_tasks(SetupHelper& helper) override {
        helper.add_task(new DbcShadowBufferTask(1, /*use_eventidx=*/true));
    }

    void fetch_custom_handles() override {
        shadow_buffer_ = setup_helper()->get<ShadowDoorbellBuffer*>("shadow_doorbell_buffer");
        eventidx_buffer_ = setup_helper()->get<ShadowDoorbellBuffer*>("eventidx_buffer");
        ASSERT_NE(shadow_buffer_, nullptr) << "DbcShadowBufferTask did not return shadow buffer";
        ASSERT_NE(eventidx_buffer_, nullptr) << "DbcShadowBufferTask did not return eventidx buffer";
    }

public:
    ShadowDoorbellBuffer* shadow_buffer() const { return shadow_buffer_; }
    ShadowDoorbellBuffer* eventidx_buffer() const { return eventidx_buffer_; }

private:
    ShadowDoorbellBuffer* shadow_buffer_{nullptr};
    ShadowDoorbellBuffer* eventidx_buffer_{nullptr};
};

DEFINE_HOST_IO_COMMON_TESTS(ShadowDoorbellSystemTest);
DEFINE_HOST_IO_PERF_TESTS(ShadowDoorbellSystemTest);

TEST_F(ShadowDoorbellSystemTest, ShadowBufferLayoutAndMapping) {
    ASSERT_EQ(shadow_buffer()->queue_count, 1);
    ASSERT_EQ(shadow_buffer()->bytes, 2 * sizeof(uint32_t));
    ASSERT_NE(shadow_buffer()->iova, 0u);
    ASSERT_NE(shadow_buffer()->host_ptr, nullptr);

    shadow_buffer()->host_ptr[0] = 7;
    shadow_buffer()->host_ptr[1] = 3;

    EXPECT_EQ(shadow_buffer()->host_ptr[0], 7u);
    EXPECT_EQ(shadow_buffer()->host_ptr[1], 3u);
}

TEST_F(ShadowDoorbellSystemTest, EventIdxBufferMirrorsUpdates) {
    ASSERT_NE(eventidx_buffer(), nullptr);
    EXPECT_EQ(eventidx_buffer()->queue_count, 1);
    EXPECT_EQ(eventidx_buffer()->bytes, 2 * sizeof(uint32_t));

    eventidx_buffer()->host_ptr[0] = 11;
    eventidx_buffer()->host_ptr[1] = 22;
    EXPECT_EQ(eventidx_buffer()->host_ptr[0], 11u);
    EXPECT_EQ(eventidx_buffer()->host_ptr[1], 22u);
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    printf("\n=== Module 55.2 Shadow Doorbell Buffer Tests ===\n");
    printf("Ensure NVME_BDF is set and VFIO is configured before running.\n\n");
    return RUN_ALL_TESTS();
}
