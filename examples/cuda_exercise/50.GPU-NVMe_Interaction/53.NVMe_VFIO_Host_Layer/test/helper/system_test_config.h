/**
 * @file system_test_config.h
 * @brief Test configuration for Module 53 system tests
 *
 * Provides reusable configuration loading from environment variables for
 * NVMe VFIO system tests. This ensures consistent configuration across all
 * system test executables.
 */

#pragma once

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <map>

// Include device selection types
#include "device/device_detector.h"

namespace nvme_test {

/**
 * @brief Invalid PCI BUS ID constant
 */
constexpr const char* INVALID_PCI_BUS_ID = "";

/**
 * @brief Host test configuration loaded from environment variables
 *
 * Loads test parameters from environment variables for Module 53 host I/O tests:
 * - NVME_BDF: PCI Bus:Device.Function (e.g., "0000:41:00.0")
 * - NVME_NSID: Namespace ID (default: 1)
 * - NVME_LBA_SIZE: Logical block size in bytes (default: 512)
 * - NVME_SLBA: Starting logical block address (default: 0)
 *
 * Default queue depths and buffer counts are provided for common test scenarios.
 */
struct HostTestConfig {
    const char* bdf{nullptr};         ///< PCI Bus:Device.Function address
    uint32_t nsid{1};                 ///< NVMe namespace ID
    uint32_t lba_size{512};           ///< Logical block size in bytes
    uint64_t slba{0};                 ///< Starting logical block address
    uint16_t sq_depth{16};            ///< Submission queue depth
    uint16_t cq_depth{16};            ///< Completion queue depth
    uint16_t num_buffers{4};          ///< Number of buffers in pool
    size_t test_bytes{0};             ///< Test size in bytes (set to lba_size * 8)

    /**
     * @brief Load configuration from environment variables or selected devices
     *
     * @param selected Optional SelectedDevices to auto-configure from (default: nullptr)
     * @param enable_log Enable logging to stdout (default: true)
     *
     * Priority order:
     * 1. Environment variables (if set)
     * 2. Selected NVMe device (if provided and env vars not set)
     * 3. Defaults
     *
     * Prints configuration summary if enable_log=true.
     */
    void load_from_env(const SelectedDevices* selected = nullptr, bool enable_log = true) {
        // Try environment first
        const char* bdf_env = std::getenv("NVME_BDF");
        if (bdf_env && strlen(bdf_env) > 0) {
            bdf = bdf_env;
        } else if (selected && selected->nvme) {
            // Auto-configure from selected NVMe device
            static std::string bdf_storage;  // Keep string alive
            bdf_storage = selected->nvme->get_pci_bus_id();
            bdf = bdf_storage.c_str();

            // Also auto-configure LBA size from device
            lba_size = selected->nvme->get_lba_size();
            if (lba_size == 0) lba_size = 512;  // Fallback
        } else {
            if (enable_log) {
                fprintf(stderr, "ERROR: NVME_BDF not set and no selected NVMe device provided\n");
                fprintf(stderr, "Example: export NVME_BDF=\"0000:41:00.0\"\n");
            }
            return;
        }

        // Override with environment variables if set
        const char* nsid_str = std::getenv("NVME_NSID");
        if (nsid_str) nsid = static_cast<uint32_t>(std::atoi(nsid_str));

        const char* lba_str = std::getenv("NVME_LBA_SIZE");
        if (lba_str) lba_size = static_cast<uint32_t>(std::atoi(lba_str));

        const char* slba_str = std::getenv("NVME_SLBA");
        if (slba_str) {
            slba = static_cast<uint64_t>(std::atoll(slba_str));
        } else {
            slba = 2000000;  // Safe default offset
        }

        // Set test bytes to 8 LBAs
        test_bytes = lba_size * 8;

        if (enable_log) {
            printf("=== Test Configuration ===\n");
            printf("  BDF:         %s\n", bdf);
            printf("  NSID:        %u\n", nsid);
            printf("  LBA Size:    %u bytes\n", lba_size);
            printf("  Start LBA:   %lu\n", slba);
            printf("  SQ Depth:    %u\n", sq_depth);
            printf("  CQ Depth:    %u\n", cq_depth);
            printf("  Pool Size:   %u buffers\n", num_buffers);
            printf("  Test Size:   %zu bytes (8 LBAs)\n", test_bytes);
            printf("==========================\n\n");
        }
    }

    /**
     * @brief Check if configuration is valid
     * @return true if BDF is set and non-empty
     */
    bool is_valid() const {
        return bdf != nullptr && strlen(bdf) > 0;
    }

    /**
     * @brief Get SetupArgs for SetupHelper
     * @return SetupArgs map with all config parameters
     *
     * Converts HostTestConfig to SetupArgs format needed by SetupHelper.
     * Includes all parameters: bdf, nsid, lba_size, slba, sq_depth, cq_depth.
     */
    std::map<std::string, std::string> get_setup_args() const {
        std::map<std::string, std::string> args;
        args["bdf"] = bdf ? bdf : "";
        args["nsid"] = std::to_string(nsid);
        args["lba_size"] = std::to_string(lba_size);
        args["slba"] = std::to_string(slba);
        args["sq_depth"] = std::to_string(sq_depth);
        args["cq_depth"] = std::to_string(cq_depth);
        return args;
    }
};

/**
 * @brief Select devices for host I/O testing with automatic fallback
 *
 * Detects all system devices and selects appropriate host and NVMe devices
 * for host I/O testing. Handles optional BDF specification for targeted
 * device selection.
 *
 * @param out_features Output: Detected system features
 * @param out_devices Output: Selected devices
 * @param out_skip_reason Output: Reason for selection failure (if any)
 * @param optional_bdf Optional: Specific NVMe BDF to target (default: nullptr)
 * @return true if suitable devices were selected, false otherwise
 *
 * Selection logic:
 * 1. Detects all system devices (host, GPUs, NVMe)
 * 2. If optional_bdf provided, adds it to requirements as specific_nvme_bdf
 * 3. Uses DeviceChooser to select best host and NVMe devices
 * 4. Validates host capabilities (VFIO, IOMMU)
 * 5. Validates NVMe device availability
 * 6. Populates out_skip_reason with detailed failure information
 *
 * Usage:
 * @code
 * SystemFeatures features;
 * SelectedDevices devices;
 * std::string skip_reason;
 * const char* target_bdf = std::getenv("NVME_BDF");
 * 
 * if (!select_test_devices(features, devices, skip_reason, target_bdf)) {
 *     GTEST_SKIP() << skip_reason;
 *     return;
 * }
 * @endcode
 */
bool select_test_devices(
    SystemFeatures& out_features,
    SelectedDevices& out_devices,
    std::string& out_skip_reason,
    const char* optional_bdf = nullptr);

}  // namespace nvme_test
