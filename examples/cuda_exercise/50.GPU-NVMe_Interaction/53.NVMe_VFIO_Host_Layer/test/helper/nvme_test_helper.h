/**
 * @file nvme_test_helper.h
 * @brief Common test helper utilities for NVMe device tests
 *
 * Provides base test fixtures and utility functions for tests that require
 * actual NVMe hardware. Handles device detection, environment variable
 * parsing, and automatic device setup/teardown.
 */

#pragma once
#include <gtest/gtest.h>
#include <filesystem>
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include "mapper/mapper_host.h"
#include "nvme_config.h"  // Test environment parsing (now in test/helper/)
// Note: File LBA utilities migrated to src/common/io/nvme_file_utils.h
// Include directly if needed: #include "common/io/nvme_file_utils.h"

namespace nvme_test {

// ============================================================================
// Environment Variable Helpers
// ============================================================================

// Environment parsing utilities for tests
// Use nvme::getenv_or, nvme::getenv_uint32, nvme::getenv_uint64 from nvme_config.h
using nvme::getenv_or;
using nvme::getenv_uint32;
using nvme::getenv_uint64;

// ============================================================================
// VFIO and Device Detection
// ============================================================================

/**
 * @brief Check if VFIO is available on the system
 *
 * @return true if /dev/vfio/vfio exists
 */
inline bool is_vfio_available() {
    return std::filesystem::exists("/dev/vfio/vfio");
}

inline std::string parse_env_value(const std::string& line, const std::string& key) {
    auto key_pos = line.find(key);
    if (key_pos == std::string::npos) return {};

    auto eq_pos = line.find('=', key_pos);
    if (eq_pos == std::string::npos) return {};

    std::string value = line.substr(eq_pos + 1);
    // Trim leading/trailing whitespace and quotes
    auto first = value.find_first_not_of(" \t\"'");
    auto last = value.find_last_not_of(" \t\r\n\"'");
    if (first == std::string::npos || last == std::string::npos) return {};
    return value.substr(first, last - first + 1);
}

inline void apply_env_file_fallback(nvme::DeviceConfig& config, const std::string& path) {
    std::ifstream file(path);
    if (!file.is_open()) return;

    std::string line;
    while (std::getline(file, line)) {
        if (config.bdf.empty() && line.find("NVME_BDF") != std::string::npos) {
            auto value = parse_env_value(line, "NVME_BDF");
            if (!value.empty()) config.bdf = value;
        }
        if (config.nsid == 0 && line.find("NVME_NSID") != std::string::npos) {
            auto value = parse_env_value(line, "NVME_NSID");
            if (!value.empty()) config.nsid = static_cast<std::uint32_t>(std::stoul(value));
        }
        if (config.lba_size == 0 && line.find("NVME_LBA_SIZE") != std::string::npos) {
            auto value = parse_env_value(line, "NVME_LBA_SIZE");
            if (!value.empty()) config.lba_size = static_cast<std::uint32_t>(std::stoul(value));
        }
        if (config.slba == 0 && line.find("NVME_SLBA") != std::string::npos) {
            auto value = parse_env_value(line, "NVME_SLBA");
            if (!value.empty()) config.slba = static_cast<std::uint64_t>(std::stoull(value));
        }
    }
}

inline void ensure_nvme_env_defaults() {
    nvme::DeviceConfig cfg = nvme::DeviceConfig::from_env();
    if (!cfg.bdf.empty()) return;  // Already configured

    std::vector<std::string> candidates;
    const char* override_path = std::getenv("NVME_ENV_FALLBACK");
    if (override_path && *override_path) {
        candidates.emplace_back(override_path);
    }
    candidates.emplace_back("/tmp/_nvme_test_env.sh");

    for (const auto& path : candidates) {
        if (!cfg.bdf.empty()) break;
        apply_env_file_fallback(cfg, path);
    }

    // Provide a safe default if nothing is configured (matches module docs)
    if (cfg.bdf.empty()) {
        cfg.bdf = "0000:09:00.0";
    }
    if (cfg.nsid == 0) {
        cfg.nsid = 1;
    }
    if (cfg.lba_size == 0) {
        cfg.lba_size = 512;
    }
    if (cfg.slba == 0) {
        cfg.slba = 1000000;
    }

    if (!cfg.bdf.empty()) {
        setenv("NVME_BDF", cfg.bdf.c_str(), 1);
    }
    if (cfg.nsid != 0) {
        setenv("NVME_NSID", std::to_string(cfg.nsid).c_str(), 1);
    }
    if (cfg.lba_size != 0) {
        setenv("NVME_LBA_SIZE", std::to_string(cfg.lba_size).c_str(), 1);
    }
    if (cfg.slba != 0) {
        setenv("NVME_SLBA", std::to_string(cfg.slba).c_str(), 1);
    }
}

/**
 * @brief Get NVMe device BDF from environment
 *
 * Tries NVME_BDF first (used by integration tests and scripts),
 * then falls back to NVME_TEST_BDF (used by unit tests).
 *
 * @return BDF string or empty if not set
 */
inline std::string get_nvme_bdf() {
    // Try NVME_BDF first (integration test environment)
    const char* bdf = std::getenv("NVME_BDF");
    if (bdf && *bdf) {
        return std::string(bdf);
    }

    // Fall back to NVME_TEST_BDF (unit test environment)
    bdf = std::getenv("NVME_TEST_BDF");
    if (bdf && *bdf) {
        return std::string(bdf);
    }

    return "";
}

/**
 * @brief Get NVMe test parameters from environment
 *
 * Extends the production DeviceConfig with test-specific parameters.
 */
struct NvmeTestParams : public nvme::DeviceConfig {
    std::uint32_t lbas;           ///< Number of LBAs for tests (default: 8)
    std::size_t test_bytes;       ///< Test size in bytes (derived)

    /// Load parameters from environment variables
    static NvmeTestParams from_env() {
        NvmeTestParams params;

        // Load base configuration from production library
        nvme::DeviceConfig base_config = nvme::DeviceConfig::from_env();
        params.bdf = base_config.bdf;
        params.nsid = base_config.nsid;
        params.lba_size = base_config.lba_size;
        params.slba = base_config.slba;

        // Apply on-disk fallback if environment variables are absent
        if (params.bdf.empty()) {
            apply_env_file_fallback(params, "/tmp/_nvme_test_env.sh");
            const char* override_path = std::getenv("NVME_ENV_FALLBACK");
            if (params.bdf.empty() && override_path && *override_path) {
                apply_env_file_fallback(params, override_path);
            }
        }

        // Handle alternative BDF environment variable for tests
        if (params.bdf.empty()) {
            params.bdf = get_nvme_bdf();
        }

        // Load test-specific parameters
        params.lbas = getenv_uint32("NVME_LBAS", 8);
        params.test_bytes = params.lbas * params.lba_size;

        // Override default SLBA if not set (test default is 1000000)
        if (params.slba == 0) {
            params.slba = 1000000;
        }

        return params;
    }
};

// ============================================================================
// Base Test Fixtures
// ============================================================================

/**
 * @brief Base test fixture for tests requiring NVMe device
 *
 * Automatically detects and opens NVMe device in SetUp(),
 * closes it in TearDown(). Skips tests if device not available.
 *
 * Usage:
 *   class MyTest : public nvme_test::NvmeDeviceTest {
 *   protected:
 *       void TestBody() {
 *           // Use this->dev, this->params
 *       }
 *   };
 */
class NvmeDeviceTest : public ::testing::Test {
protected:
    NvmeDevice* dev = nullptr;      ///< NVMe device handle
    NvmeTestParams params;          ///< Test parameters from environment

    void SetUp() override {
        // Check VFIO availability
        if (!is_vfio_available()) {
            GTEST_SKIP() << "VFIO not available (/dev/vfio/vfio not found). "
                         << "Load vfio kernel modules or run tests with appropriate permissions.";
        }

        // Load parameters from environment
        params = NvmeTestParams::from_env();

        // Skip if no device configured
        if (!params.is_valid()) {
            GTEST_SKIP() << "NVMe device not configured. Set NVME_BDF or NVME_TEST_BDF environment variable. "
                         << "Example: export NVME_BDF=0000:01:00.0";
        }

        // Open NVMe device with default queue sizes
        dev = nvme_open(params.bdf.c_str(), 16, 64, params.lba_size);
        ASSERT_NE(dev, nullptr)
            << "Failed to open NVMe device at " << params.bdf
            << ". Ensure device is bound to vfio-pci and you have permissions.";
    }

    void TearDown() override {
        if (dev) {
            nvme_close(dev);
            dev = nullptr;
        }
    }
};

/**
 * @brief Test fixture with custom queue sizes
 *
 * Allows customization of submission and completion queue sizes.
 * Use this when you need specific queue configurations.
 */
class NvmeDeviceTestCustomQueues : public ::testing::Test {
protected:
    NvmeDevice* dev = nullptr;
    NvmeTestParams params;
    std::uint16_t sq_entries = 16;  ///< SQ size (override in subclass)
    std::uint16_t cq_entries = 64;  ///< CQ size (override in subclass)

    void SetUp() override {
        if (!is_vfio_available()) {
            GTEST_SKIP() << "VFIO not available (/dev/vfio/vfio not found)";
        }

        params = NvmeTestParams::from_env();
        if (!params.is_valid()) {
            GTEST_SKIP() << "NVMe device not configured. Set NVME_BDF or NVME_TEST_BDF.";
        }

        dev = nvme_open(params.bdf.c_str(), sq_entries, cq_entries, params.lba_size);
        ASSERT_NE(dev, nullptr) << "Failed to open NVMe device at " << params.bdf;
    }

    void TearDown() override {
        if (dev) {
            nvme_close(dev);
            dev = nullptr;
        }
    }
};

/**
 * @brief Lightweight test fixture for tests that don't need device
 *
 * Only checks VFIO availability and environment variables,
 * doesn't actually open the device. Use for API tests or
 * tests that manually control device lifetime.
 */
class NvmeTestEnvironment : public ::testing::Test {
protected:
    NvmeTestParams params;

    void SetUp() override {
        if (!is_vfio_available()) {
            GTEST_SKIP() << "VFIO not available (/dev/vfio/vfio not found)";
        }

        params = NvmeTestParams::from_env();
        if (!params.is_valid()) {
            GTEST_SKIP() << "NVMe device not configured. Set NVME_BDF or NVME_TEST_BDF.";
        }
    }
};

// ============================================================================
// Test Utilities
// ============================================================================

/**
 * @brief Print NVMe test environment information
 *
 * Helper for debugging test setup issues.
 */
inline void print_test_env() {
    auto params = NvmeTestParams::from_env();
    std::fprintf(stderr, "\n=== NVMe Test Environment ===\n");
    std::fprintf(stderr, "  BDF:          %s\n", params.bdf.c_str());
    std::fprintf(stderr, "  NSID:         %u\n", params.nsid);
    std::fprintf(stderr, "  LBA Size:     %u bytes\n", params.lba_size);
    std::fprintf(stderr, "  Test SLBA:    %lu\n", params.slba);
    std::fprintf(stderr, "  Test LBAs:    %u\n", params.lbas);
    std::fprintf(stderr, "  Test Bytes:   %zu\n", params.test_bytes);
    std::fprintf(stderr, "  VFIO:         %s\n", is_vfio_available() ? "Available" : "NOT AVAILABLE");
    std::fprintf(stderr, "=============================\n\n");
}

} // namespace nvme_test
