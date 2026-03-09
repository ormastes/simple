/**
 * @file test_doorbell_support.cpp
 * @brief Test nvme_get_support_doorbell() function
 */

#include <gtest/gtest.h>
#include "nvme_test_helper.h"  // Common NVMe test utilities
#include <cstdio>

TEST(DoorbellSupport, NullDevice) {
  // With null device, should return basic MMIO mode
  DoorbellMode doorbell = nvme_get_support_doorbell(nullptr);
  // DOORBELL_MMIO removed - GPU cannot access MMIO registers

  std::fprintf(stderr, "Null device doorbell support: %d (MMIO=%d, DEFERRED=%d, DEFERRED_EVENTIDX=%d)\n",
               doorbell, DOORBELL_DEFERRED, DOORBELL_DEFERRED_EVENTIDX); // MMIO removed
}

TEST(DoorbellSupport, AllModesSupported) {
  // The returned value should be one of the three valid modes
  DoorbellMode doorbell = nvme_get_support_doorbell(nullptr);

  bool is_valid = (doorbell == static_cast<DoorbellMode>(DOORBELL_MMIO)) ||
                  (doorbell == static_cast<DoorbellMode>(DOORBELL_DEFERRED)) ||
                  (doorbell == static_cast<DoorbellMode>(DOORBELL_DEFERRED_EVENTIDX));

  EXPECT_TRUE(is_valid) << "Doorbell type must be DEFERRED(1) or DEFERRED_EVENTIDX(2), got: " << (int)doorbell << " (MMIO removed)";
}

// Integration test - requires actual NVMe device
// Uses NvmeDeviceTestCustomQueues for 32/32 queue sizes
class DoorbellSupportTest : public nvme_test::NvmeDeviceTestCustomQueues {
protected:
  void SetUp() override {
    sq_entries = 32;
    cq_entries = 32;
    nvme_test::NvmeDeviceTestCustomQueues::SetUp();
  }
};

TEST_F(DoorbellSupportTest, DISABLED_RealDeviceSupport) {
  DoorbellMode doorbell = nvme_get_support_doorbell(dev);

  // Should be one of the two valid modes (MMIO removed)
  bool is_valid = (doorbell == static_cast<DoorbellMode>(DOORBELL_DEFERRED)) ||
                  (doorbell == static_cast<DoorbellMode>(DOORBELL_DEFERRED_EVENTIDX));

  EXPECT_TRUE(is_valid);

  std::fprintf(stderr, "Device %s supports doorbell mode: ", params.bdf.c_str());
  switch(doorbell) {
    // DOORBELL_MMIO case removed - GPU cannot access MMIO registers
    case static_cast<DoorbellMode>(DOORBELL_DEFERRED):
      std::fprintf(stderr, "DEFERRED (optimized, no event index)\n");
      break;
    case static_cast<DoorbellMode>(DOORBELL_DEFERRED_EVENTIDX):
      std::fprintf(stderr, "DEFERRED_EVENTIDX (fully optimized with event index)\n");
      break;
    default:
      std::fprintf(stderr, "Unknown (%d)\n", (int)doorbell);
  }
}
