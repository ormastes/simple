/**
 * @file vfio_utils.h
 * @brief VFIO utility functions for automatic device binding
 *
 * Provides helpers for tests to automatically bind/unbind NVMe devices
 * using the passwordless sudo helper scripts installed by quick_setup.sh
 */

#ifndef VFIO_UTILS_H
#define VFIO_UTILS_H

#include <string>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include "vfio_safety.h"  // Test safety checks (now in test/helper/)

namespace vfio_utils {

/**
 * @brief Check if NVMe device is safe to bind to VFIO
 *
 * SAFETY CHECKS (delegated to vfio::check_binding_safety):
 * - Not a boot device
 * - Not mounted
 * - No filesystem or partitions
 *
 * @param bdf PCI bus:device.function
 * @param error_msg Output: error message if unsafe
 * @return true if safe to bind
 */
inline bool is_safe_to_bind(const std::string& bdf, std::string& error_msg) {
    // Use production safety check library
    auto safety = vfio::check_binding_safety(bdf);
    if (!safety.is_safe()) {
        error_msg = safety.error_msg;
        return false;
    }
    return true;
}

/**
 * @brief Ensure NVMe device is bound to vfio-pci driver
 *
 * Uses /usr/local/sbin/vfio-bind.sh (installed by quick_setup.sh)
 * which can be called with passwordless sudo.
 *
 * SAFETY: Performs multiple checks before binding to prevent
 * accidentally binding boot device or device with filesystem.
 *
 * @param bdf PCI bus:device.function (e.g., "0000:41:00.0")
 * @param bound_by_us Output: true if we bound it (need to unbind later)
 * @param error_msg Output: error message if binding fails
 * @return true if device is bound to vfio-pci, false on error
 */
inline bool ensure_vfio_binding(const std::string& bdf, bool& bound_by_us, std::string& error_msg) {
    bound_by_us = false;

    // SAFETY CHECK: Verify device is safe to bind
    if (!is_safe_to_bind(bdf, error_msg)) {
        return false;  // Error message already set
    }

    // Check if vfio-bind.sh helper exists
    if (access("/usr/local/sbin/vfio-bind.sh", X_OK) != 0) {
        error_msg = "vfio-bind.sh not found. Run: sudo ./scripts/quick_setup.sh";
        return false;
    }

    // Check current driver
    std::string driver_path = "/sys/bus/pci/devices/" + bdf + "/driver";
    char link_target[256];
    ssize_t len = readlink(driver_path.c_str(), link_target, sizeof(link_target) - 1);

    if (len > 0) {
        link_target[len] = '\0';
        std::string current_driver = link_target;

        // Already bound to vfio-pci?
        if (current_driver.find("vfio-pci") != std::string::npos) {
            return true;  // Already bound, nothing to do
        }
    }

    // Need to bind - call helper script (fail fast if sudo password is required)
    std::string cmd = "/usr/local/sbin/vfio-bind.sh " + bdf + " 2>&1";
    if (geteuid() != 0) {
        cmd = "sudo -n " + cmd;
    }
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        error_msg = "Failed to execute vfio-bind.sh";
        return false;
    }

    char buffer[256];
    std::string output;
    while (fgets(buffer, sizeof(buffer), pipe)) {
        output += buffer;
    }

    int status = pclose(pipe);
    if (status != 0) {
        if (output.find("password is required") != std::string::npos ||
            output.find("a password") != std::string::npos) {
            error_msg = "vfio-bind.sh requires passwordless sudo. Run scripts/quick_setup.sh or rerun tests with sudo -E.";
        } else {
            error_msg = "vfio-bind.sh failed: " + output;
        }
        return false;
    }

    bound_by_us = true;
    return true;
}

/**
 * @brief Restore device to original driver
 *
 * Only unbinds if we bound it originally.
 *
 * @param bdf PCI bus:device.function
 * @param we_bound_it Only unbind if true
 */
inline void restore_original_driver(const std::string& bdf, bool we_bound_it) {
    if (!we_bound_it) {
        return;  // We didn't bind it, don't unbind
    }

    if (access("/usr/local/sbin/vfio-unbind.sh", X_OK) != 0) {
        return;  // Helper not available
    }

    std::string cmd = "/usr/local/sbin/vfio-unbind.sh " + bdf + " 2>&1";
    if (geteuid() != 0) {
        cmd = "sudo -n " + cmd;
    }
    system(cmd.c_str());
}

} // namespace vfio_utils

#endif // VFIO_UTILS_H
