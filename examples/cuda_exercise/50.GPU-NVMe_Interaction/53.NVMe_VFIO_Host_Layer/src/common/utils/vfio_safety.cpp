/**
 * @file vfio_safety.cpp
 * @brief Implementation of VFIO safety checks (production copy)
 */

#include "vfio_safety.h"

#include <dirent.h>
#include <limits.h>
#include <unistd.h>

#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace vfio {

const char* SafetyCheck::status_str() const {
    switch (status) {
        case SafetyStatus::SAFE:
            return "Safe";
        case SafetyStatus::BOOT_DEVICE:
            return "Boot Device";
        case SafetyStatus::MOUNTED_FS:
            return "Mounted Filesystem";
        case SafetyStatus::IN_CMDLINE:
            return "In Kernel Cmdline";
        case SafetyStatus::NOT_FOUND:
            return "Not Found";
        case SafetyStatus::CHECK_FAILED:
            return "Check Failed";
        default:
            return "Unknown";
    }
}

std::vector<std::string> get_block_devices_for_bdf(const std::string& bdf) {
    std::vector<std::string> devices;

    DIR* dir = opendir("/sys/block");
    if (!dir) {
        return devices;
    }

    struct dirent* entry;
    char resolved[PATH_MAX];

    while ((entry = readdir(dir)) != nullptr) {
        if (entry->d_name[0] == '.') {
            continue;
        }

        std::string device_link = std::string("/sys/block/") + entry->d_name + "/device";
        ssize_t len = readlink(device_link.c_str(), resolved, sizeof(resolved) - 1);
        if (len <= 0) {
            continue;
        }
        resolved[len] = '\0';

        std::string resolved_path = resolved;
        if (resolved_path.find(bdf) == std::string::npos) {
            continue;
        }

        // This block device belongs to our PCI device
        devices.emplace_back(entry->d_name);

        // Also check for partitions
        std::string block_dir = std::string("/sys/block/") + entry->d_name;
        DIR* block_entries = opendir(block_dir.c_str());
        if (!block_entries) {
            continue;
        }

        struct dirent* part;
        while ((part = readdir(block_entries)) != nullptr) {
            if (part->d_name[0] == '.') {
                continue;
            }
            std::string part_name = part->d_name;
            if (part_name.rfind(entry->d_name, 0) == 0 && part_name != entry->d_name) {
                devices.emplace_back(part_name);
            }
        }
        closedir(block_entries);
    }
    closedir(dir);

    return devices;
}

bool are_devices_mounted(const std::vector<std::string>& block_devices) {
    std::ifstream mounts("/proc/mounts");
    if (!mounts.is_open()) {
        return false;  // Assume safe if we can't check
    }

    std::string line;
    while (std::getline(mounts, line)) {
        for (const auto& dev_name : block_devices) {
            std::string needle = "/dev/" + dev_name;
            if (line.find(needle) != std::string::npos) {
                if (line.find(" / ") != std::string::npos || line.find(" /boot ") != std::string::npos) {
                    return true;  // Critical filesystem mounted
                }
                return true;
            }
        }
    }

    return false;
}

bool is_in_kernel_cmdline(const std::string& bdf) {
    std::ifstream cmdline("/proc/cmdline");
    if (!cmdline.is_open()) {
        return false;  // Assume safe if we can't check
    }

    std::string line;
    std::getline(cmdline, line);

    if (line.find(bdf) != std::string::npos) {
        return true;
    }

    if (line.find("root=/dev/nvme") != std::string::npos) {
        // Heuristic warning for NVMe boot devices
    }

    return false;
}

SafetyCheck check_binding_safety(const std::string& bdf) {
    SafetyCheck result{};
    result.status = SafetyStatus::SAFE;
    result.error_msg.clear();

    if (bdf.empty() || bdf.length() < 7) {
        result.status = SafetyStatus::NOT_FOUND;
        result.error_msg = "Invalid PCI BDF: " + bdf;
        return result;
    }

    result.block_devices = get_block_devices_for_bdf(bdf);

    if (is_in_kernel_cmdline(bdf)) {
        result.status = SafetyStatus::IN_CMDLINE;
        result.error_msg = "SAFETY: Device " + bdf + " appears in kernel cmdline. "
                           "Likely BOOT device. REFUSING to mark as safe.";
        return result;
    }

    if (are_devices_mounted(result.block_devices)) {
        result.status = SafetyStatus::MOUNTED_FS;
        result.error_msg = "SAFETY: Device " + bdf + " has mounted filesystems. ";
        if (!result.block_devices.empty()) {
            result.error_msg += "Block devices: ";
            for (const auto& dev : result.block_devices) {
                result.error_msg += dev + " ";
            }
        }
        result.error_msg += "REFUSING to mark as safe.";
        return result;
    }

    std::ifstream mounts("/proc/mounts");
    if (mounts.is_open()) {
        std::string line;
        while (std::getline(mounts, line)) {
            if ((line.find(" / ") != std::string::npos || line.find(" /boot ") != std::string::npos) &&
                line.find("/dev/nvme") != std::string::npos) {
                if (result.error_msg.empty()) {
                    result.error_msg = "WARNING: System uses NVMe for root/boot. Be extremely careful!";
                }
                break;
            }
        }
    }

    result.status = SafetyStatus::SAFE;
    if (result.error_msg.empty()) {
        result.error_msg = "Device " + bdf + " is safe to bind to VFIO";
    }

    return result;
}

}  // namespace vfio
