#include <gtest/gtest.h>
#include "nvme_test_helper.h"  // Common NVMe test utilities
#include "memory/host_memory_buffer.h"  // For backward compatibility aliases

/**
 * @brief Test for host-pinned consecutive buffer creation
 *
 * Uses NvmeDeviceTest fixture for automatic device setup/teardown
 */
class HostPinnedBufferTest : public nvme_test::NvmeDeviceTest {};

TEST_F(HostPinnedBufferTest, CreateAndDestroy){
  Buffer* buf = host_create_consecutive_buffer(64 * 1024);
  ASSERT_NE(buf, nullptr);
  EXPECT_NE(buf->addr, nullptr);
  EXPECT_EQ(buf->mem_type, MemoryType::PINNED_HOST);  // Host pinned memory
  EXPECT_EQ(buf->consecutive, Consecutive::CONSECUTIVE);  // Consecutive buffer
  EXPECT_EQ((reinterpret_cast<std::uintptr_t>(buf->addr) & 4095u), 0u); // page aligned
  EXPECT_NE(buf->iova, 0u);

  host_buffer_destroy(buf);
}
