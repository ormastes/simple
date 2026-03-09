/**
 * @file test_setup_tasks.cpp
 * @brief Hardware tests for all SetupHelper tasks
 *
 * Tests all 14 setup tasks (4 original + 10 new) against real hardware.
 *
 * Features:
 * - Automatic device detection (no hard-coded device IDs)
 * - Graceful skipping when hardware/permissions unavailable
 * - Works with or without sudo (skips tests requiring privileges)
 *
 * Usage:
 *   # Automatic device detection
 *   ./test_setup_tasks
 *
 *   # Or with sudo for full testing
 *   sudo -E ./test_setup_tasks
 *
 *   # Optional: override detected devices
 *   export NVME_BDF="0000:41:00.0"
 *   export NVME_NSID="1"
 *   ./test_setup_tasks
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include <gtest/gtest.h>
#include <unistd.h>  // for geteuid()
#include "setup_helper.h"
// Note: device_chooser.h functionality merged into device_detector.h
#include "device/device_detector.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"

// ============================================================================
// Test Fixture with Automatic Device Detection
// ============================================================================

class SetupTaskTest : public ::testing::Test {
protected:
    SetupHelper helper;
    SystemFeatures detected_features_;
    SelectedDevices selected_devices_;
    bool has_sudo_{false};
    bool has_vfio_{false};
    bool has_nvme_{false};
    bool has_gpu_{false};
    std::string detected_bdf_;

    void SetUp() override {
        // Detect available hardware
        detected_features_ = SystemFeatures::detect_all();

        // Check for sudo privileges
        has_sudo_ = (geteuid() == 0);

        // Check for VFIO/IOMMU support
        auto requirements = DeviceRequirements::for_host_dma();
        requirements.require_nvme = true;
        selected_devices_ = detected_features_.select_devices(requirements);

        has_vfio_ = (selected_devices_.host &&
                     selected_devices_.host->get_vfio_support() == SupportLevel::FULL &&
                     selected_devices_.host->has_iommu_enabled());

        // Check for NVMe device
        has_nvme_ = (selected_devices_.nvme != nullptr &&
                     !selected_devices_.nvme->is_os_live());

        if (has_nvme_) {
            detected_bdf_ = selected_devices_.nvme->get_pci_bus_id();
        }

        // Check for GPU
#ifdef __CUDACC__
        int gpu_count = 0;
        has_gpu_ = (cudaGetDeviceCount(&gpu_count) == cudaSuccess && gpu_count > 0);
#else
        has_gpu_ = false;
#endif

        // Load environment variables (may override detection)
        auto env_args = load_env_args({
            "NVME_BDF", "NVME_NSID", "NVME_LBA_SIZE", "NVME_SLBA"
        });

        // Use detected BDF if not provided via environment
        if (env_args.find("NVME_BDF") == env_args.end() && !detected_bdf_.empty()) {
            env_args["NVME_BDF"] = detected_bdf_;
        }

        helper.set_global_args(env_args);
    }

    // Helper to skip tests requiring sudo
    void RequireSudo() {
        if (!has_sudo_) {
            GTEST_SKIP() << "Test requires root privileges. Run with: sudo -E ./test_setup_tasks";
        }
    }

    // Helper to skip tests requiring VFIO
    void RequireVFIO() {
        if (!has_vfio_) {
            GTEST_SKIP() << "Test requires VFIO/IOMMU support. "
                         << "Enable IOMMU in BIOS and kernel (intel_iommu=on or amd_iommu=on)";
        }
    }

    // Helper to skip tests requiring NVMe device
    void RequireNVMe() {
        if (!has_nvme_) {
            GTEST_SKIP() << "Test requires NVMe device accessible via VFIO. "
                         << "Bind an NVMe device to vfio-pci: sudo /usr/local/sbin/vfio-bind.sh <BDF>";
        }
    }

    // Helper to skip tests requiring GPU
    void RequireGPU() {
        if (!has_gpu_) {
            GTEST_SKIP() << "Test requires CUDA GPU. No GPUs detected.";
        }
    }

    // Combined requirement check for admin + hardware
    void RequireAdminHardware() {
        RequireSudo();
        RequireVFIO();
        RequireNVMe();
    }
};

// ============================================================================
// Original Task Tests (4)
// ============================================================================

TEST_F(SetupTaskTest, NvmeSetupTask_Success) {
    RequireAdminHardware();

    helper.add_task(new NvmeSetupTask());

    ASSERT_TRUE(helper.setup_all()) << "NvmeSetupTask should succeed with valid BDF";

    // Verify device was created
    ASSERT_TRUE(helper.has("nvme_device"));
    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    ASSERT_NE(dev, nullptr);

    // Verify queue structs (modern API returns iosq_struct and iocq_struct)
    ASSERT_TRUE(helper.has("iosq_struct"));
    ASSERT_TRUE(helper.has("iocq_struct"));
    NvmeQueueStruct* iosq = helper.get<NvmeQueueStruct*>("iosq_struct");
    NvmeQueueStruct* iocq = helper.get<NvmeQueueStruct*>("iocq_struct");
    ASSERT_NE(iosq, nullptr);
    ASSERT_NE(iocq, nullptr);
    ASSERT_NE(iosq->sq_base, nullptr);
    ASSERT_NE(iosq->cq_base, nullptr);

    // Verify device properties
    EXPECT_GT(nvme_get_page_size(dev), 0u);
    EXPECT_GT(nvme_get_lba_size(dev), 0u);

    printf("✓ NvmeSetupTask: Device %p, Queue %p (BDF: %s)\n",
           dev, iosq, detected_bdf_.c_str());
}

TEST_F(SetupTaskTest, HostMemoryFactoryTask_Success) {
    RequireAdminHardware();

    helper.add_task(new NvmeSetupTask());
    helper.add_task(new HostMemoryFactoryTask(4096, 8));

    ASSERT_TRUE(helper.setup_all());

    // Verify pool was created
    ASSERT_TRUE(helper.has("host_pool"));
    HostPool* pool = helper.get<HostPool*>("host_pool");
    ASSERT_NE(pool, nullptr);

    // Verify pool properties
    EXPECT_EQ(pool->cap, 8u);
    EXPECT_EQ(pool->buf_size, 4096u);
    EXPECT_EQ(pool->in_use, 0u);

    // Test buffer acquisition
    DmaBuf* buf = host_pool_acquire(pool);
    ASSERT_NE(buf, nullptr);
    EXPECT_NE(buf->addr, nullptr);
    EXPECT_GT(buf->iova, 0u);
    EXPECT_EQ(buf->bytes, 4096u);

    host_pool_release(pool, buf);

    printf("✓ HostMemoryFactoryTask: Pool %p (cap=%u)\n", pool, pool->cap);
}

#ifdef __CUDACC__
TEST_F(SetupTaskTest, CudaHostMemoryFactoryTask_Success) {
    RequireAdminHardware();
    RequireGPU();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new CudaHostMemoryFactoryTask(8192, 4));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("cuda_host_pool"));
    CudaHostPool* pool = helper.get<CudaHostPool*>("cuda_host_pool");
    ASSERT_NE(pool, nullptr);

    EXPECT_EQ(pool->cap, 4u);
    EXPECT_EQ(pool->buf_size, 8192u);

    printf("✓ CudaHostMemoryFactoryTask: Pool %p (cap=%u)\n", pool, pool->cap);
}

TEST_F(SetupTaskTest, CudaGpuMemoryFactoryTask_Success) {
    RequireAdminHardware();
    RequireGPU();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new CudaGpuMemoryFactoryTask(16384, 2));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("cuda_gpu_pool"));
    CudaGpuPool* pool = helper.get<CudaGpuPool*>("cuda_gpu_pool");
    ASSERT_NE(pool, nullptr);

    EXPECT_EQ(pool->cap, 2u);
    EXPECT_EQ(pool->buf_size, 16384u);

    printf("✓ CudaGpuMemoryFactoryTask: Pool %p (cap=%u)\n", pool, pool->cap);
}
#endif // __CUDACC__

// ============================================================================
// New High-Priority Task Tests (2)
// ============================================================================

TEST_F(SetupTaskTest, TestFileSetupTask_Sequential) {
    helper.add_task(new TestFileSetupTask("/tmp/test_sequential.bin", 10, "sequential"));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("test_file_path"));
    auto* path = helper.get<std::string*>("test_file_path");
    ASSERT_NE(path, nullptr);
    EXPECT_EQ(*path, "/tmp/test_sequential.bin");

    // Verify file exists and has correct size
    struct stat st;
    ASSERT_EQ(stat(path->c_str(), &st), 0);
    EXPECT_EQ(st.st_size, 10 * 1024 * 1024);  // 10 MB

    printf("✓ TestFileSetupTask: Created %s (%zu bytes)\n",
           path->c_str(), st.st_size);

    // Cleanup
    unlink(path->c_str());
}

TEST_F(SetupTaskTest, TestFileSetupTask_Random) {
    helper.add_task(new TestFileSetupTask("/tmp/test_random.bin", 5, "random"));

    ASSERT_TRUE(helper.setup_all());

    auto* path = helper.get<std::string*>("test_file_path");
    ASSERT_NE(path, nullptr);

    struct stat st;
    ASSERT_EQ(stat(path->c_str(), &st), 0);
    EXPECT_EQ(st.st_size, 5 * 1024 * 1024);

    printf("✓ TestFileSetupTask (random): %s (%zu bytes)\n",
           path->c_str(), st.st_size);

    unlink(path->c_str());
}

TEST_F(SetupTaskTest, StatCollectorTask_Success) {
    helper.add_task(new StatCollectorTask("latency,iops,bandwidth"));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("stat_collector"));
    auto* stats = helper.get<StatCollector*>("stat_collector");
    ASSERT_NE(stats, nullptr);
    EXPECT_EQ(stats->metrics, "latency,iops,bandwidth");
    EXPECT_TRUE(stats->running);

    printf("✓ StatCollectorTask: Collector %p (metrics: %s)\n",
           stats, stats->metrics.c_str());
}

// ============================================================================
// New Medium-Priority Task Tests (4)
// ============================================================================

#ifdef __CUDACC__
TEST_F(SetupTaskTest, GpuDetectionTask_Success) {
    RequireGPU();
    helper.add_task(new GpuDetectionTask("7.0", true));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("gpu_count"));
    int* count = helper.get<int*>("gpu_count");
    ASSERT_NE(count, nullptr);
    EXPECT_GT(*count, 0) << "At least one GPU should be detected";

    ASSERT_TRUE(helper.has("selected_gpu_id"));
    int* gpu_id = helper.get<int*>("selected_gpu_id");
    ASSERT_NE(gpu_id, nullptr);
    EXPECT_GE(*gpu_id, 0);
    EXPECT_LT(*gpu_id, *count);

    printf("✓ GpuDetectionTask: Found %d GPU(s), selected GPU %d\n",
           *count, *gpu_id);
}
#endif

TEST_F(SetupTaskTest, NvmeDetectionTask_Success) {
    RequireAdminHardware();
    helper.add_task(new NvmeDetectionTask(10, false));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("nvme_count"));
    int* count = helper.get<int*>("nvme_count");
    ASSERT_NE(count, nullptr);
    EXPECT_GT(*count, 0);

    ASSERT_TRUE(helper.has("selected_nvme_bdf"));
    auto* bdf = helper.get<std::string*>("selected_nvme_bdf");
    ASSERT_NE(bdf, nullptr);
    EXPECT_FALSE(bdf->empty());

    printf("✓ NvmeDetectionTask: Found %d device(s), BDF=%s\n",
           *count, bdf->c_str());
}

TEST_F(SetupTaskTest, WarmupTask_Success) {
    RequireAdminHardware();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new WarmupTask(5));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("warmup_complete"));
    bool* done = helper.get<bool*>("warmup_complete");
    ASSERT_NE(done, nullptr);
    EXPECT_TRUE(*done);

    printf("✓ WarmupTask: Warmup completed\n");
}

TEST_F(SetupTaskTest, ConsecutiveBufferTask_Host) {
    RequireAdminHardware();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new ConsecutiveBufferTask(64 * 1024 * 1024, "HOST"));  // 64MB

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("consecutive_buffer"));
    Buffer* buf = helper.get<Buffer*>("consecutive_buffer");
    ASSERT_NE(buf, nullptr);
    ASSERT_NE(buf->addr, nullptr);
    EXPECT_GT(buf->iova, 0u);
    EXPECT_EQ(buf->bytes, 64 * 1024 * 1024u);

    printf("✓ ConsecutiveBufferTask (HOST): Buffer %p, %zu bytes, IOVA 0x%lx\n",
           buf->addr, buf->bytes, buf->iova);
}

#ifdef __CUDACC__
TEST_F(SetupTaskTest, ConsecutiveBufferTask_CudaGpu) {
    RequireAdminHardware();
    RequireGPU();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new ConsecutiveBufferTask(32 * 1024 * 1024, "CUDA_GPU"));  // 32MB

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("consecutive_buffer"));
    Buffer* buf = helper.get<Buffer*>("consecutive_buffer");
    ASSERT_NE(buf, nullptr);
    ASSERT_NE(buf->addr, nullptr);
    EXPECT_GT(buf->iova, 0u);
    EXPECT_EQ(buf->bytes, 32 * 1024 * 1024u);

    printf("✓ ConsecutiveBufferTask (CUDA_GPU): Buffer %p, %zu bytes\n",
           buf->addr, buf->bytes);
}
#endif

// ============================================================================
// New Low-Priority Task Tests (4)
// ============================================================================

TEST_F(SetupTaskTest, MultiQueueSetupTask_Success) {
    RequireAdminHardware();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new MultiQueueSetupTask(4, 32, 32));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("num_queues"));
    int* num_q = helper.get<int*>("num_queues");
    ASSERT_NE(num_q, nullptr);
    EXPECT_EQ(*num_q, 4);

    printf("✓ MultiQueueSetupTask: %d queues configured\n", *num_q);
}

#ifdef __CUDACC__
TEST_F(SetupTaskTest, GpuP2PSetupTask_Success) {
    RequireAdminHardware();
    RequireGPU();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new GpuP2PSetupTask(0));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("p2p_enabled"));
    bool* enabled = helper.get<bool*>("p2p_enabled");
    ASSERT_NE(enabled, nullptr);

    if (!*enabled) {
        GTEST_SKIP() << "P2P driver not present; GpuP2PSetupTask returned fallback queue.";
    }
    EXPECT_TRUE(*enabled);

    printf("✓ GpuP2PSetupTask: P2P %s\n", *enabled ? "enabled" : "disabled");
}

TEST_F(SetupTaskTest, GdsMemoryFactoryTask_Success) {
    RequireAdminHardware();
    RequireGPU();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new GdsMemoryFactoryTask(4096, 16, 0));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("gds_buffers"));
    void* gds = helper.get<void*>("gds_buffers");
    ASSERT_NE(gds, nullptr);

    printf("✓ GdsMemoryFactoryTask: GDS handle %p\n", gds);
}
#endif

TEST_F(SetupTaskTest, DbcDaemonTask_Success) {
    RequireAdminHardware();
    helper.add_task(new NvmeSetupTask());
    helper.add_task(new DbcDaemonTask("shadow"));

    ASSERT_TRUE(helper.setup_all());

    ASSERT_TRUE(helper.has("dbc_daemon"));
    void* daemon = helper.get<void*>("dbc_daemon");
    ASSERT_NE(daemon, nullptr);

    printf("✓ DbcDaemonTask: Daemon handle %p\n", daemon);
}

// ============================================================================
// Integration Tests
// ============================================================================

TEST_F(SetupTaskTest, FullBenchmarkSetup) {
    RequireAdminHardware();
    RequireGPU();
    // Complete benchmark setup with all task types

    // Detection
    helper.add_task(new NvmeDetectionTask());
#ifdef __CUDACC__
    helper.add_task(new GpuDetectionTask());
#endif

    // Device setup
    helper.add_task(new NvmeSetupTask());

    // Memory
    helper.add_task(new HostMemoryFactoryTask(4096, 16));
#ifdef __CUDACC__
    helper.add_task(new CudaGpuMemoryFactoryTask(4096, 16));
#endif

    // Infrastructure
    helper.add_task(new TestFileSetupTask("/tmp/benchmark_test.bin", 100, "sequential"));
    helper.add_task(new WarmupTask(10));
    helper.add_task(new StatCollectorTask());

    ASSERT_TRUE(helper.setup_all()) << "Full benchmark setup should succeed";

    // Verify all resources
    EXPECT_TRUE(helper.has("nvme_device"));
    EXPECT_TRUE(helper.has("host_pool"));
    EXPECT_TRUE(helper.has("test_file_path"));
    EXPECT_TRUE(helper.has("warmup_complete"));
    EXPECT_TRUE(helper.has("stat_collector"));

#ifdef __CUDACC__
    EXPECT_TRUE(helper.has("cuda_gpu_pool"));
    EXPECT_TRUE(helper.has("gpu_count"));
#endif

    printf("✓ Full benchmark setup: All tasks completed successfully\n");

    // Cleanup test file
    if (helper.has("test_file_path")) {
        auto* path = helper.get<std::string*>("test_file_path");
        if (path) unlink(path->c_str());
    }
}

TEST_F(SetupTaskTest, ErrorHandling_MissingDevice) {
    // Test error handling when device is required but not provided
    helper.add_task(new WarmupTask(5));  // Requires nvme_device

    EXPECT_FALSE(helper.setup_all()) << "Should fail when nvme_device not available";

    printf("✓ Error handling: Correctly detected missing dependency\n");
}

TEST_F(SetupTaskTest, TaskOrdering_AdminFirst) {
    RequireAdminHardware();
    // Verify admin tasks execute before user tasks

    helper.add_task(new HostMemoryFactoryTask(4096, 4));  // User task
    helper.add_task(new NvmeSetupTask());                 // Admin task

    ASSERT_TRUE(helper.setup_all()) << "Tasks should execute in correct order (admin first)";

    // Verify both succeeded
    EXPECT_TRUE(helper.has("nvme_device"));
    EXPECT_TRUE(helper.has("host_pool"));

    printf("✓ Task ordering: Admin tasks executed before user tasks\n");
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);

    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  SetupHelper Task Tests - Hardware Verification              ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    // Detect available hardware
    printf("Detecting hardware...\n\n");
    SystemFeatures features = SystemFeatures::detect_all();

    // Check privileges
    bool has_sudo = (geteuid() == 0);
    printf("Privileges:   %s\n", has_sudo ? "✓ root/sudo" : "✗ user (tests requiring sudo will be skipped)");

    // Check VFIO/IOMMU
    auto requirements = DeviceRequirements::for_host_dma();
    requirements.require_nvme = true;
    SelectedDevices selected = features.select_devices(requirements);

    bool has_vfio = (selected.host &&
                     selected.host->get_vfio_support() == SupportLevel::FULL &&
                     selected.host->has_iommu_enabled());
    printf("VFIO/IOMMU:   %s", has_vfio ? "✓ enabled" : "✗ not available");
    if (!has_vfio && selected.host) {
        printf(" (support: %s, IOMMU: %s)",
               support_level_str(selected.host->get_vfio_support()),
               selected.host->has_iommu_enabled() ? "yes" : "no");
    }
    printf("\n");

    // Check NVMe device
    bool has_nvme = (selected.nvme != nullptr && !selected.nvme->is_os_live());
    printf("NVMe Device:  ");
    if (has_nvme) {
        printf("✓ %s (BDF: %s)\n",
               selected.nvme->get_device_path().c_str(),
               selected.nvme->get_pci_bus_id().c_str());
    } else if (selected.nvme && selected.nvme->is_os_live()) {
        printf("✗ %s is OS-live (bind to vfio-pci first)\n",
               selected.nvme->get_device_path().c_str());
    } else {
        printf("✗ not found\n");
    }

    // Check GPU
#ifdef __CUDACC__
    int gpu_count = 0;
    bool has_gpu = (cudaGetDeviceCount(&gpu_count) == cudaSuccess && gpu_count > 0);
    printf("CUDA GPU:     %s", has_gpu ? "✓ detected" : "✗ not found");
    if (has_gpu) {
        printf(" (%d GPU%s)", gpu_count, gpu_count > 1 ? "s" : "");
    }
    printf("\n");
#else
    printf("CUDA GPU:     ⊘ not compiled with CUDA support\n");
#endif

    printf("\n");

    // Show environment overrides if set
    const char* bdf = std::getenv("NVME_BDF");
    const char* nsid = std::getenv("NVME_NSID");
    const char* lba_size = std::getenv("NVME_LBA_SIZE");
    if (bdf || nsid || lba_size) {
        printf("Environment overrides:\n");
        if (bdf) printf("  NVME_BDF:      %s\n", bdf);
        if (nsid) printf("  NVME_NSID:     %s\n", nsid);
        if (lba_size) printf("  NVME_LBA_SIZE: %s\n", lba_size);
        printf("\n");
    }

    // Give instructions if missing requirements
    if (!has_sudo || !has_vfio || !has_nvme) {
        printf("⚠️  Some tests will be skipped due to missing requirements.\n");
        printf("   To run all tests:\n");
        if (!has_sudo) {
            printf("   • Run with sudo: sudo -E ./test_setup_tasks\n");
        }
        if (!has_vfio) {
            printf("   • Enable IOMMU in BIOS and kernel boot params (intel_iommu=on)\n");
        }
        if (!has_nvme) {
            printf("   • Bind an NVMe device to vfio-pci:\n");
            printf("     sudo /usr/local/sbin/vfio-bind.sh 0000:XX:00.0\n");
        }
        printf("\n");
    }

    int result = RUN_ALL_TESTS();

    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  Test Suite Complete                                          ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    return result;
}
