#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include "mapper/mapper_host.h"

namespace {

class GpuCqProvisioningTest : public ::testing::Test {
protected:
    void SetUp() override {
        if (access("/dev/vfio/vfio", R_OK | W_OK) != 0) {
            GTEST_SKIP() << "VFIO not available on this host";
        }
        const char* bdf = getenv("NVME_BDF");
        if (!bdf || bdf[0] == '\0') {
            GTEST_SKIP() << "NVME_BDF not set";
        }
        dev_ = nvme_open(bdf, /*admin_qd=*/64, /*io_qd=*/64, /*item_size_bytes=*/4096);
        if (!dev_) {
            GTEST_SKIP() << "Failed to open NVMe device";
        }
    }

    void TearDown() override {
        if (dev_) {
            nvme_close(dev_);
            dev_ = nullptr;
        }
    }

    NvmeDevice* dev_{nullptr};
};

TEST_F(GpuCqProvisioningTest, RejectsMissingIova) {
    if (!dev_) GTEST_SKIP();

    void* cq_dev_ptr = nullptr;
    ASSERT_EQ(cudaMalloc(&cq_dev_ptr, 4096 * 64), cudaSuccess);

    // Pass an invalid IOVA (0) to confirm the API fails gracefully instead of crashing.
    int rc = nvme_create_gpu_cq(dev_, /*cqid=*/2, cq_dev_ptr, /*gpu_cq_iova=*/0, /*entries=*/64);
    EXPECT_NE(rc, 0);

    cudaFree(cq_dev_ptr);
}

}  // namespace

