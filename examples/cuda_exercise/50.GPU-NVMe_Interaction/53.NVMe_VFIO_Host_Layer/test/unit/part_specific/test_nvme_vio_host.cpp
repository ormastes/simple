#include <gtest/gtest.h>
#include "nvme_test_helper.h"  // Common NVMe test utilities

/**
 * @brief Test fixture for NVMe VIO host tests
 *
 * Uses standard NvmeDeviceTest for automatic device setup/teardown
 */
class NvmeVioHostTest : public nvme_test::NvmeDeviceTest {};

TEST_F(NvmeVioHostTest, OpenAndQueues){
  Queue* iosq = nvme_get_iosq(dev);
  Queue* iocq = nvme_get_iocq(dev);
  ASSERT_NE(iosq, nullptr); ASSERT_NE(iocq, nullptr);
  EXPECT_EQ(iosq->entry_size, 64u);
  EXPECT_EQ(iocq->entry_size, 16u);
}

// NOTE: This test is disabled because the os_* file LBA functions were removed during
// helper migration. The functionality moved to nvme::io:: namespace but needs
// a file creation function (os_make_consecutive_file_with_pattern) that doesn't exist yet.
// Disabled until production library supports file pattern creation
/*
TEST(NvmeVioHost, FileLBABasics){
  std::string path = nvme_test::getenv_or("TEST_DIR","/tmp") + "/nvme_lba_demo.bin";
  ASSERT_GE(os_make_consecutive_file_with_pattern(path.c_str(), 64*1024, 4096), 0);
  long long n = os_file_lbas(path.c_str(), 512, nullptr, 0);
  ASSERT_GT(n, 0);
  int rc = os_file_lbas_is_consecutive(path.c_str(), 512, nullptr, nullptr);
  ASSERT_GE(rc, 0);
}
*/
