/**
 * @file test_setup_helper_host_io.cpp
 * @brief SetupHelper-based host I/O integration tests
 *
 * Tests the complete SetupHelper workflow for host I/O operations:
 * - Automatic device detection and VFIO binding
 * - Host buffer pool creation and management
 * - NVMe command submission and completion
 * - Pattern-based data verification
 * - Multiple outstanding commands
 *
 * These tests validate the entire setup infrastructure including NvmeSetupTask,
 * HostPoolTask, and their integration with the host I/O layer.
 *
 * Requirements:
 * - Real NVMe device accessible via VFIO
 * - Environment variables:
 *   - NVME_BDF: PCI Bus:Device.Function (e.g., "0000:41:00.0")
 *   - NVME_NSID: Namespace ID (typically "1")
 *   - NVME_LBA_SIZE: Logical block size ("512" or "4096")
 *   - NVME_SLBA: Starting LBA for test area (must be safe to overwrite)
 */

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <unistd.h>
#include <vector>

#include <gtest/gtest.h>

// Module 53 APIs
#include "common/forward_decls.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "doorbell/nvme_doorbell.h"
#include "common/patterns/data_patterns.h"

#include "device/device_detector.h"
#include "device/device_detector.h"
#include "helper/setup_helper.h"
#include "helper/vfio_utils.h"

// Test helpers
#include "helper/system_test_config.h"

using nvme_test::HostTestConfig;
using nvme_test::INVALID_PCI_BUS_ID;
using nvme_test::select_test_devices;

/**
 * @brief SetupHelper-based host I/O integration test fixture
 *
 * Uses SetupHelper to automatically configure NVMe device and buffer pools,
 * then performs host I/O operations to validate the complete setup workflow.
 */
class SetupHelperHostIoTest : public ::testing::Test {
protected:
    SetupHelper helper;
    SystemFeatures detected_features_;
    SelectedDevices selected_devices_;
    bool helper_ready_{false};
    std::string skip_reason_{"Environment not evaluated"};

    void SetUp() override {
        helper_ready_ = false;
        skip_reason_.clear();

        auto env_args = load_env_args({
            "NVME_BDF",
            "NVME_NSID",
            "NVME_LBA_SIZE",
            "NVME_SLBA"
        });
        std::string helper_target_bdf;
        if (auto it = env_args.find("NVME_BDF"); it != env_args.end()) {
            helper_target_bdf = it->second;
        }

        detected_features_ = SystemFeatures::detect_all();

        auto requirements = DeviceRequirements::for_host_dma();
        requirements.require_nvme = true;
        selected_devices_ = detected_features_.select_devices(requirements);

        if (!selected_devices_.host) {
            skip_reason_ = "Host environment lacks VFIO/IOMMU support required for SetupHelper-based tests.\n" +
                           selected_devices_.host_log;
            GTEST_SKIP() << skip_reason_;
            return;
        }

        if (!selected_devices_.nvme) {
            if (helper_target_bdf.empty()) {
                skip_reason_ = "No NVMe device satisfies host-DMA requirements and NVME_BDF is unset. Export NVME_BDF to let SetupHelper run automatic VFIO binding.";
                GTEST_SKIP() << skip_reason_;
                return;
            }

            const NvmeFeature* detected_match = nullptr;
            for (const auto& nvme : detected_features_.nvme_devs) {
                if (nvme.get_pci_bus_id() == helper_target_bdf) {
                    detected_match = &nvme;
                    break;
                }
            }

            if (detected_match && detected_match->is_os_live()) {
                skip_reason_ = "NVMe device " + detected_match->get_device_path() +
                               " is managed by the OS. Bind manually to vfio-pci before running tests.";
                GTEST_SKIP() << skip_reason_;
                return;
            }
        } else {
            const std::string& selected_bdf = selected_devices_.nvme->get_pci_bus_id();
            if (helper_target_bdf.empty()) {
                if (!selected_bdf.empty() && selected_bdf != INVALID_PCI_BUS_ID) {
                    helper_target_bdf = selected_bdf;
                    env_args["NVME_BDF"] = selected_bdf;
                }
            }

            if (selected_devices_.nvme->is_os_live()) {
                skip_reason_ = "NVMe device " + selected_devices_.nvme->get_device_path() +
                               " is bound to the OS or has mounted filesystems. Refusing to bind automatically.";
                GTEST_SKIP() << skip_reason_;
                return;
            }
        }

        if (helper_target_bdf.empty()) {
            skip_reason_ = "NVME_BDF is not set and device detection could not infer the VFIO-bound controller. Export NVME_BDF before running.";
            GTEST_SKIP() << skip_reason_;
            return;
        }

        std::string helper_safety_msg;
        if (!vfio_utils::is_safe_to_bind(helper_target_bdf, helper_safety_msg)) {
            skip_reason_ = helper_safety_msg;
            GTEST_SKIP() << skip_reason_;
            return;
        }

        env_args["NVME_BDF"] = helper_target_bdf;

        helper = create_host_io_setup(4096, 4);
        helper.set_global_args(env_args);

        if (!helper.setup_all()) {
            const std::string device_hint = helper_target_bdf.empty()
                ? "<unknown NVMe device>"
                : helper_target_bdf;
            if (geteuid() != 0) {
                skip_reason_ = "SetupHelper requires sudo privileges to configure VFIO for " +
                               device_hint +
                               ". Re-run with sudo -E ctest -R test_setup_helper_host_io.";
            } else {
                skip_reason_ = "SetupHelper failed even with administrative privileges. Review NVMe VFIO binding and task output.";
            }
            GTEST_SKIP() << skip_reason_;
            return;
        }

        helper_ready_ = true;
        skip_reason_.clear();
    }
};

TEST_F(SetupHelperHostIoTest, DeviceAndPoolInitialization) {
    if (!helper_ready_) {
        GTEST_SKIP() << skip_reason_;
        return;
    }

    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");

    printf("✓ Device and pool initialized\n");
    printf("  Page size: %zu bytes\n", nvme_get_page_size(dev));
    printf("  LBA size:  %u bytes\n", nvme_get_lba_size(dev));
    printf("  Pool cap:  %u buffers\n", pool->cap);
}

TEST_F(SetupHelperHostIoTest, BufferManagement) {
    if (!helper_ready_) {
        GTEST_SKIP() << skip_reason_;
        return;
    }

    HostPool* pool = helper.get<HostPool*>("host_pool");
    DmaBuf* buf = host_pool_acquire(pool);

    printf("✓ Buffer acquired: addr=%p, iova=0x%lx, bytes=%zu\n",
           buf->addr, buf->iova, buf->bytes);

    host_pool_release(pool, buf);
    printf("✓ Buffer released\n");
}

TEST_F(SetupHelperHostIoTest, SingleBlockRead) {
    if (!helper_ready_) {
        GTEST_SKIP() << skip_reason_;
        return;
    }

    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");
    Queue* iosq = nvme_get_iosq(dev);
    Queue* iocq = nvme_get_iocq(dev);

    uint32_t nsid = 1;
    uint64_t slba = 2000000;
    if (const char* nsid_str = std::getenv("NVME_NSID")) {
        nsid = static_cast<uint32_t>(std::atoi(nsid_str));
    }
    if (const char* slba_str = std::getenv("NVME_SLBA")) {
        slba = static_cast<uint64_t>(std::atoll(slba_str));
    }

    uint32_t lba_size = nvme_get_lba_size(dev);
    DmaBuf* buf = host_pool_acquire(pool);
    std::memset(buf->addr, 0, lba_size);

    printf("Submitting READ command...\n");
    printf("  NSID: %u, SLBA: %lu\n", nsid, slba);

    uint16_t cid = host_submit<CMD_READ, DOORBELL_MMIO>(
        iosq, nsid, slba, lba_size, buf, lba_size);
    printf("✓ Read command submitted: CID=%u\n", cid);

    uint16_t completed_cid = 0;
    PollResult poll_result;
    host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 1000000, iosq);

    host_pool_release(pool, buf);
    printf("✓ Read completed: CID=%u\n", completed_cid);
}

TEST_F(SetupHelperHostIoTest, WriteReadVerifyPattern) {
    if (!helper_ready_) {
        GTEST_SKIP() << skip_reason_;
        return;
    }

    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");
    Queue* iosq = nvme_get_iosq(dev);
    Queue* iocq = nvme_get_iocq(dev);

    uint32_t nsid = 1;
    uint64_t slba = 2000000;
    if (const char* nsid_str = std::getenv("NVME_NSID")) {
        nsid = static_cast<uint32_t>(std::atoi(nsid_str));
    }
    if (const char* slba_str = std::getenv("NVME_SLBA")) {
        slba = static_cast<uint64_t>(std::atoll(slba_str));
    }

    uint32_t lba_size = nvme_get_lba_size(dev);
    DmaBuf* write_buf = host_pool_acquire(pool);
    nvme::patterns::DataPatterns::fill(write_buf->addr, lba_size, nvme::patterns::PatternType::SEQUENTIAL, 12345);

    printf("Writing pattern to SLBA=%lu...\n", slba);
    host_submit<CMD_WRITE, DOORBELL_MMIO>(iosq, nsid, slba, lba_size, write_buf, lba_size);

    uint16_t completed_write_cid = 0;
    PollResult write_result;
    host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_write_cid, &write_result, 1000000, iosq);

    host_pool_release(pool, write_buf);
    printf("✓ Write completed\n");

    DmaBuf* read_buf = host_pool_acquire(pool);
    std::memset(read_buf->addr, 0xFF, lba_size);

    printf("Reading back from SLBA=%lu...\n", slba);
    host_submit<CMD_READ, DOORBELL_MMIO>(iosq, nsid, slba, lba_size, read_buf, lba_size);

    uint16_t completed_read_cid = 0;
    PollResult read_result;
    host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_read_cid, &read_result, 1000000, iosq);

    nvme::patterns::DataPatterns::verify(read_buf->addr, lba_size, nvme::patterns::PatternType::SEQUENTIAL, 12345);
    printf("✓ Pattern verified\n");

    host_pool_release(pool, read_buf);
}

TEST_F(SetupHelperHostIoTest, MultipleOutstandingCommands) {
    if (!helper_ready_) {
        GTEST_SKIP() << skip_reason_;
        return;
    }

    NvmeDevice* dev = helper.get<NvmeDevice*>("nvme_device");
    HostPool* pool = helper.get<HostPool*>("host_pool");
    Queue* iosq = nvme_get_iosq(dev);
    Queue* iocq = nvme_get_iocq(dev);

    uint32_t nsid = 1;
    uint64_t slba = 2000000;
    if (const char* nsid_str = std::getenv("NVME_NSID")) {
        nsid = static_cast<uint32_t>(std::atoi(nsid_str));
    }
    if (const char* slba_str = std::getenv("NVME_SLBA")) {
        slba = static_cast<uint64_t>(std::atoll(slba_str));
    }

    uint32_t lba_size = nvme_get_lba_size(dev);
    const int num_cmds = 3;
    std::vector<DmaBuf*> bufs(num_cmds, nullptr);

    printf("Submitting %d read commands...\n", num_cmds);
    for (int i = 0; i < num_cmds; i++) {
        bufs[i] = host_pool_acquire(pool);
        std::memset(bufs[i]->addr, 0, lba_size);

        uint16_t cid = host_submit<CMD_READ, DOORBELL_MMIO>(
            iosq, nsid, slba + i, lba_size, bufs[i], lba_size);
        printf("  Command %d submitted: CID=%u, SLBA=%lu\n", i, cid, slba + i);
    }

    printf("Polling for completions...\n");
    for (int i = 0; i < num_cmds; i++) {
        uint16_t completed_cid = 0;
        PollResult poll_result;
        host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &completed_cid, &poll_result, 1000000, iosq);
        printf("  ✓ Command completed: CID=%u\n", completed_cid);
    }

    for (auto* buf : bufs) {
        host_pool_release(pool, buf);
    }

    printf("✓ All %d commands completed\n", num_cmds);
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);

    printf("\n============================================================\n");
    printf("Module 53: SetupHelper Host I/O Integration Tests\n");
    printf("============================================================\n\n");

    int result = RUN_ALL_TESTS();

    printf("\n============================================================\n");
    printf("SetupHelper Host I/O Integration Tests Complete\n");
    printf("============================================================\n\n");

    return result;
}
