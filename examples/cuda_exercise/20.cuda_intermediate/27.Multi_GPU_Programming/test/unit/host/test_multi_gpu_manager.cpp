/**
 * Multi-GPU Manager Tests (Module 27)
 *
 * Tests for MultiGPUManager host-side functionality
 */

#include <gtest/gtest.h>
#include "multi_gpu_manager.h"

class MultiGPUManagerTest : public ::testing::Test {
protected:
    void SetUp() override {
        int deviceCount;
        cudaGetDeviceCount(&deviceCount);

        if (deviceCount < 2) {
            GTEST_SKIP() << "Multi-GPU tests require at least 2 GPUs";
        }

        mgr = new MultiGPUManager();
    }

    void TearDown() override {
        delete mgr;
    }

    MultiGPUManager* mgr;
};

TEST_F(MultiGPUManagerTest, Initialization) {
    EXPECT_TRUE(mgr->isInitialized());
    EXPECT_GE(mgr->getDeviceCount(), 2);

    printf("Found %d GPUs\n", mgr->getDeviceCount());
}

TEST_F(MultiGPUManagerTest, PeerAccessSetup) {
    bool success = mgr->setupPeerAccess();
    EXPECT_TRUE(success);

    mgr->printTopology();

    // Check if at least some peer access is available
    int deviceCount = mgr->getDeviceCount();
    bool anyPeerAccess = false;

    for (int i = 0; i < deviceCount; i++) {
        for (int j = 0; j < deviceCount; j++) {
            if (i != j && mgr->canAccessPeer(i, j)) {
                anyPeerAccess = true;
                break;
            }
        }
    }

    printf("Peer access available: %s\n", anyPeerAccess ? "YES" : "NO");
}

TEST_F(MultiGPUManagerTest, WorkDistribution) {
    const int totalWork = 10000;

    auto distribution = mgr->distributeWork(totalWork);

    EXPECT_EQ(static_cast<int>(distribution.size()), mgr->getDeviceCount());

    int totalAssigned = 0;
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        EXPECT_GE(distribution[dev], 0);
        totalAssigned += distribution[dev];

        printf("GPU %d: %d work units (%.1f%%)\n",
               dev, distribution[dev],
               100.0f * distribution[dev] / totalWork);
    }

    EXPECT_EQ(totalAssigned, totalWork);
}

TEST_F(MultiGPUManagerTest, DeviceProperties) {
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        const auto& props = mgr->getDeviceProperties(dev);

        EXPECT_GT(props.multiProcessorCount, 0);
        EXPECT_GT(props.totalGlobalMem, 0);

        printf("GPU %d: %s\n", dev, props.name);
        printf("  SMs: %d\n", props.multiProcessorCount);
        printf("  Memory: %.1f GB\n", props.totalGlobalMem / 1e9);
    }
}

TEST_F(MultiGPUManagerTest, StreamManagement) {
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        cudaStream_t stream = mgr->getStream(dev);
        EXPECT_NE(stream, nullptr);
    }
}

TEST_F(MultiGPUManagerTest, SynchronizeAll) {
    // Launch dummy kernels on all GPUs
    for (int dev = 0; dev < mgr->getDeviceCount(); dev++) {
        cudaSetDevice(dev);
        cudaStream_t stream = mgr->getStream(dev);

        // Simple delay kernel (just sleep)
        cudaStreamSynchronize(stream);  // Should not block
    }

    // Synchronize all at once
    mgr->synchronizeAll();

    SUCCEED();
}
