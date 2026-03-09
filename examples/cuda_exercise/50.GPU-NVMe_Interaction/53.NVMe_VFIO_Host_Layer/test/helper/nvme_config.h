/**
 * @file nvme_config.h
 * @brief NVMe configuration utilities and environment variable parsing
 *
 * Provides utilities for parsing NVMe device configuration from environment
 * variables and configuration structures for NVMe device parameters.
 */

#pragma once

#include <string>
#include <cstdlib>
#include <cstdint>
#include <cstring>

namespace nvme {

/**
 * @brief Get environment variable value or return default
 *
 * @param key Environment variable name
 * @param default_value Default value if not set
 * @return Environment value or default
 */
inline std::string getenv_or(const char* key, const char* default_value) {
    const char* value = std::getenv(key);
    return value ? std::string(value) : std::string(default_value);
}

/**
 * @brief Get environment variable as integer or return default
 *
 * @param key Environment variable name
 * @param default_value Default value if not set
 * @return Environment value parsed as integer or default
 */
inline std::uint32_t getenv_uint32(const char* key, std::uint32_t default_value) {
    const char* value = std::getenv(key);
    return value ? static_cast<std::uint32_t>(std::strtoul(value, nullptr, 0)) : default_value;
}

/**
 * @brief Get environment variable as uint64_t or return default
 *
 * @param key Environment variable name
 * @param default_value Default value if not set
 * @return Environment value parsed as uint64_t or default
 */
inline std::uint64_t getenv_uint64(const char* key, std::uint64_t default_value) {
    const char* value = std::getenv(key);
    return value ? static_cast<std::uint64_t>(std::strtoull(value, nullptr, 0)) : default_value;
}

/**
 * @brief NVMe device configuration parameters
 *
 * Contains all necessary parameters for NVMe device access:
 * - PCI Bus:Device.Function (BDF)
 * - Namespace ID
 * - LBA (Logical Block Address) size
 * - Starting LBA for test operations
 */
struct DeviceConfig {
    std::string bdf;        ///< PCI BDF (e.g., "0000:41:00.0")
    std::uint32_t nsid;     ///< Namespace ID (typically 1)
    std::uint32_t lba_size; ///< LBA size in bytes (e.g., 512, 4096)
    std::uint64_t slba;     ///< Starting LBA for operations

    /**
     * @brief Create configuration from environment variables
     *
     * Reads the following environment variables:
     * - NVME_BDF: PCI Bus:Device.Function
     * - NVME_NSID: Namespace ID (default: 1)
     * - NVME_LBA_SIZE: LBA size in bytes (default: 512)
     * - NVME_SLBA: Starting LBA (default: 0)
     *
     * @return DeviceConfig populated from environment
     */
    static DeviceConfig from_env() {
        DeviceConfig config;
        config.bdf = getenv_or("NVME_BDF", "");
        config.nsid = getenv_uint32("NVME_NSID", 1);
        config.lba_size = getenv_uint32("NVME_LBA_SIZE", 512);
        config.slba = getenv_uint64("NVME_SLBA", 0);
        return config;
    }

    /**
     * @brief Check if configuration is valid
     *
     * @return true if BDF is non-empty and LBA size is valid
     */
    bool is_valid() const {
        return !bdf.empty() &&
               (lba_size == 512 || lba_size == 4096 || lba_size == 8192);
    }

    /**
     * @brief Get configuration summary string
     *
     * @return Human-readable configuration summary
     */
    std::string to_string() const {
        return "BDF=" + bdf +
               " NSID=" + std::to_string(nsid) +
               " LBA_SIZE=" + std::to_string(lba_size) +
               " SLBA=" + std::to_string(slba);
    }
};

}  // namespace nvme