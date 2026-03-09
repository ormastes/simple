/**
 * @file vfio_safety.h
 * @brief VFIO safety validation utilities
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

    /**
     * @brief Check if device is safe to bind
     * @return true if status is SAFE
     */
    bool is_safe() const { return status == SafetyStatus::SAFE; }

    /**
     * @brief Get human-readable status string
     * @return Status as string
     */
    const char* status_str() const;
};

/**
 * @brief Check if NVMe device is safe to bind to VFIO
 *
 * Performs comprehensive safety checks:
 * - Not a boot device (not in kernel cmdline)
 * - Not mounted (no filesystems mounted from device)
 * - No partitions in use
 *
 * @param bdf PCI Bus:Device.Function (e.g., "0000:41:00.0")
 * @return SafetyCheck result with status and details
 *
 * @note This function only checks safety. It does NOT modify the system.
 *       Actual binding should be done by test setup tasks or applications.
 *
 * @code
 * auto check = vfio::check_binding_safety("0000:41:00.0");
 * if (check.is_safe()) {
 *     // Safe to bind device to VFIO
 * } else {
 *     printf("Cannot bind: %s\n", check.error_msg.c_str());
 * }
 * @endcode
 */
SafetyCheck check_binding_safety(const std::string& bdf);

/**
 * @brief Get list of block devices associated with PCI device
 *
 * Finds all block devices (nvme0n1, nvme0n1p1, etc.) that belong
 * to the specified PCI device.
 *
 * @param bdf PCI Bus:Device.Function
 * @return Vector of block device names (without /dev/ prefix)
 */
std::vector<std::string> get_block_devices_for_bdf(const std::string& bdf);

/**
 * @brief Check if any block device is mounted
 *
 * @param block_devices List of block device names (e.g., "nvme0n1", "nvme0n1p1")
 * @return true if any device is mounted
 */
bool are_devices_mounted(const std::vector<std::string>& block_devices);

/**
 * @brief Check if device appears in kernel command line
 *
 * Checks /proc/cmdline for references to the device,
 * which would indicate it's used for boot.
 *
 * @param bdf PCI Bus:Device.Function
 * @return true if device appears in kernel cmdline
 */
bool is_in_kernel_cmdline(const std::string& bdf);

}  // namespace vfio