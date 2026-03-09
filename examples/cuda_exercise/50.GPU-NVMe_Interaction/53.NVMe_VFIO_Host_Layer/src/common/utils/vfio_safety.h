/**
 * @file vfio_safety.h
 * @brief VFIO safety validation utilities (production copy)
 *
 * Provides safety checks to prevent accidental binding of critical devices
 * to VFIO. These checks ensure devices are safe to use for testing/P2P.
 */

#pragma once

#include <string>
#include <vector>

namespace vfio {

/**
 * @brief Safety status enumeration
 */
enum class SafetyStatus {
    SAFE,           ///< Device is safe to bind to VFIO
    BOOT_DEVICE,    ///< Device is boot/root device
    MOUNTED_FS,     ///< Device has mounted filesystems
    IN_CMDLINE,     ///< Device appears in kernel command line
    NOT_FOUND,      ///< Device not found in system
    CHECK_FAILED    ///< Safety check failed
};

/**
 * @brief Safety check result
 */
struct SafetyCheck {
    SafetyStatus status;                    ///< Safety status
    std::string error_msg;                  ///< Detailed error message if not safe
    std::vector<std::string> block_devices; ///< Associated block devices

    /// @brief Check if device is safe to bind
    bool is_safe() const { return status == SafetyStatus::SAFE; }

    /// @brief Get human-readable status string
    const char* status_str() const;
};

/// Check if NVMe device is safe to bind to VFIO
SafetyCheck check_binding_safety(const std::string& bdf);
/// Get list of block devices associated with PCI device
std::vector<std::string> get_block_devices_for_bdf(const std::string& bdf);
/// Check if any block device is mounted
bool are_devices_mounted(const std::vector<std::string>& block_devices);
/// Check if device appears in kernel command line
bool is_in_kernel_cmdline(const std::string& bdf);

}  // namespace vfio
