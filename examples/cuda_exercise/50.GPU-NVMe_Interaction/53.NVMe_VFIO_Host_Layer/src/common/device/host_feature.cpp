/**
 * @file host_feature.cpp
 * @brief Host feature detection implementation
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "host_feature.h"
#include <cstdio>
#include <cstring>
#include <sstream>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/utsname.h>
#include <sys/stat.h>
#include <sys/sysinfo.h>

HostFeature::HostFeature() {
    detect_iommu();
    detect_vfio();
    detect_p2p();
    detect_kernel_info();
    detect_os_info();
    detect_memory();
    detect_privileges();
}

void HostFeature::detect_iommu() {
    // Check for IOMMU hardware (Intel VT-d or AMD-Vi)
    // Look for DMAR table (Intel) or AMD IOMMU in dmesg/sysfs

    // Method 1: Check /sys/kernel/iommu_groups
    DIR* dir = opendir("/sys/kernel/iommu_groups");
    if (dir) {
        iommu_hardware_ = true;

        // Count IOMMU groups
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            if (entry->d_name[0] != '.') {
                iommu_group_count_++;
            }
        }
        closedir(dir);
    }

    // Method 2: Check kernel command line for iommu enablement
    bool acs_param_set = false;
    FILE* f = fopen("/proc/cmdline", "r");
    if (f) {
        char cmdline[4096];
        if (fgets(cmdline, sizeof(cmdline), f)) {
            if (strstr(cmdline, "iommu=on") ||
                strstr(cmdline, "intel_iommu=on") ||
                strstr(cmdline, "amd_iommu=on")) {
                iommu_enabled_ = true;
            }

            // Check for ACS override kernel parameter
            if (strstr(cmdline, "pci=noacs") ||
                strstr(cmdline, "pcie_acs_override")) {
                acs_param_set = true;
            }
        }
        fclose(f);
    }

    // Method 3: Check dmesg for IOMMU messages (requires root)
    if (!iommu_enabled_ && iommu_hardware_) {
        // If hardware exists but not explicitly enabled, check if it's on by default
        // On modern systems, IOMMU is often enabled by default
        if (iommu_group_count_ > 0) {
            iommu_enabled_ = true;
        }
    }

    // Method 4: Check actual PCIe ACS state
    // Read PCIe configuration to verify ACS is actually disabled
    bool acs_actually_disabled = false;

    // Check all PCIe devices for ACS state
    // Focus on bridges and switches which typically enforce ACS
    DIR* pci_dir = opendir("/sys/bus/pci/devices");
    if (pci_dir) {
        struct dirent* entry;
        while ((entry = readdir(pci_dir)) != nullptr) {
            if (entry->d_name[0] == '.') continue;

            string bdf = entry->d_name;
            // Check if this device has ACS disabled
            if (check_acs_state_for_device(bdf)) {
                acs_actually_disabled = true;
                // If we find any device with ACS disabled, that's good enough
                // (means ACS override is working)
                break;
            }
        }
        closedir(pci_dir);
    }

    // Set acs_override_ to true if:
    // 1. Kernel parameter is set (user intent), OR
    // 2. Actual PCIe ACS is disabled (verified state)
    acs_override_ = acs_param_set || acs_actually_disabled;
}

bool HostFeature::check_acs_state_for_device(const string& bdf) {
    // Read PCIe config space to check ACS (Access Control Services) state
    // ACS Capability ID = 0x000D (in extended capabilities at offset 0x100+)
    // Returns true if ACS is disabled (good for P2P), false if enabled or unknown

    string config_path = "/sys/bus/pci/devices/" + bdf + "/config";
    int fd = open(config_path.c_str(), O_RDONLY);
    if (fd < 0) {
        // Can't read config (permission denied or device doesn't exist)
        return false;
    }

    // PCIe extended capabilities start at offset 0x100
    uint8_t ext_cap_space[4096 - 0x100];
    if (pread(fd, ext_cap_space, sizeof(ext_cap_space), 0x100) < 0) {
        close(fd);
        return false;
    }
    close(fd);

    // Search for ACS capability (ID = 0x000D)
    uint32_t offset = 0;
    while (offset < sizeof(ext_cap_space) - 4) {
        uint16_t cap_id = *(uint16_t*)(ext_cap_space + offset);
        uint16_t cap_next = *(uint16_t*)(ext_cap_space + offset + 2);

        if (cap_id == 0x000D) {  // Found ACS capability
            // ACS Control Register is at offset + 6 (after cap header + acs capability)
            if (offset + 8 > sizeof(ext_cap_space)) break;

            uint16_t acs_ctrl = *(uint16_t*)(ext_cap_space + offset + 6);

            // Check if ACS enforcement bits are disabled
            // Bits that block P2P: SV(0), TB(1), RR(2), CR(3), UF(4), EC(5), DT(6)
            // For P2P to work, these should be 0 (disabled)
            const uint16_t ACS_P2P_BLOCKING_BITS = 0x7F;  // Bits 0-6

            if ((acs_ctrl & ACS_P2P_BLOCKING_BITS) == 0) {
                // ACS is disabled (all blocking bits are 0)
                return true;
            } else {
                // ACS is enabled and may block P2P
                return false;
            }
        }

        // No ACS capability found or end of capability list
        if (cap_id == 0x0000 || cap_id == 0xFFFF) break;

        // Move to next capability (next pointer is in upper 12 bits of cap_next)
        uint32_t next_offset = (cap_next >> 4) & 0xFFF;
        if (next_offset == 0 || next_offset <= offset) break;

        offset = next_offset - 0x100;  // Adjust for our buffer offset
    }

    // No ACS capability found - this is actually good for P2P
    // (device doesn't support ACS, so it can't block P2P)
    return true;
}

void HostFeature::detect_vfio() {
    // Check if VFIO kernel module is loaded
    FILE* f = fopen("/proc/modules", "r");
    if (f) {
        char line[256];
        while (fgets(line, sizeof(line), f)) {
            if (strstr(line, "vfio ") || strstr(line, "vfio_pci ")) {
                vfio_module_loaded_ = true;
                break;
            }
        }
        fclose(f);
    }

    // Determine VFIO support level
    if (!iommu_hardware_) {
        vfio_support_ = SupportLevel::NOT_SUPPORTED;
    } else if (!iommu_enabled_) {
        vfio_support_ = SupportLevel::HARDWARE_ONLY;
    } else if (!vfio_module_loaded_) {
        vfio_support_ = SupportLevel::PARTIAL;
    } else {
        // Check if /dev/vfio/vfio exists and is accessible
        if (access("/dev/vfio/vfio", R_OK | W_OK) == 0) {
            vfio_support_ = SupportLevel::FULL;
        } else {
            // Module loaded but device not accessible (permissions?)
            vfio_support_ = SupportLevel::PARTIAL;
        }
    }
}

void HostFeature::detect_p2p() {
    // Check if gpu_p2p_nvme kernel module is loaded
    FILE* f = fopen("/proc/modules", "r");
    if (f) {
        char line[256];
        while (fgets(line, sizeof(line), f)) {
            if (strstr(line, "gpu_p2p_nvme ")) {
                p2p_module_loaded_ = true;
                break;
            }
        }
        fclose(f);
    }

    // Determine P2P support level
    if (vfio_support_ == SupportLevel::NOT_SUPPORTED) {
        p2p_support_ = SupportLevel::NOT_SUPPORTED;
    } else if (vfio_support_ == SupportLevel::HARDWARE_ONLY) {
        p2p_support_ = SupportLevel::HARDWARE_ONLY;
    } else if (!p2p_module_loaded_) {
        p2p_support_ = SupportLevel::PARTIAL;
    } else {
        // Check if /dev/gpu_p2p_nvme exists
        if (access("/dev/gpu_p2p_nvme", R_OK | W_OK) == 0) {
            p2p_support_ = SupportLevel::FULL;
        } else {
            p2p_support_ = SupportLevel::PARTIAL;
        }
    }
}

void HostFeature::detect_kernel_info() {
    struct utsname uts;
    if (uname(&uts) == 0) {
        kernel_version_ = string(uts.release);
    }
}

void HostFeature::detect_os_info() {
    // Try to read /etc/os-release
    FILE* f = fopen("/etc/os-release", "r");
    if (f) {
        char line[256];
        while (fgets(line, sizeof(line), f)) {
            if (strncmp(line, "PRETTY_NAME=", 12) == 0) {
                // Extract value between quotes
                char* start = strchr(line, '"');
                if (start) {
                    start++;
                    char* end = strchr(start, '"');
                    if (end) {
                        *end = '\0';
                        os_name_ = start;
                    }
                }
                break;
            }
        }
        fclose(f);
    }

    if (os_name_.empty()) {
        os_name_ = "Unknown Linux";
    }
}

void HostFeature::detect_memory() {
    struct sysinfo info {};
    if (sysinfo(&info) == 0) {
        total_memory_bytes_ = static_cast<uint64_t>(info.totalram) *
                              static_cast<uint64_t>(info.mem_unit);
    }
}

void HostFeature::detect_privileges() {
    // Check if running as root
    has_admin_ = (geteuid() == 0);

    // Could also check for CAP_SYS_ADMIN capability, but root check is simpler
}

string HostFeature::get_name() const {
    return "Host System";
}

string HostFeature::get_description() const {
    stringstream ss;

    ss << "Host System: " << os_name_ << "\n";
    ss << "  Kernel: " << kernel_version_ << "\n";
    if (total_memory_bytes_ > 0) {
        ss << "  Memory: " << (total_memory_bytes_ / (1024.0 * 1024 * 1024))
           << " GB\n";
    }
    ss << "  IOMMU Hardware: " << (iommu_hardware_ ? "Present" : "Not Found") << "\n";
    ss << "  IOMMU Enabled: " << (iommu_enabled_ ? "Yes" : "No") << "\n";

    if (iommu_hardware_) {
        ss << "  IOMMU Groups: " << iommu_group_count_ << "\n";
    }

    ss << "  VFIO Support: " << support_level_str(vfio_support_) << "\n";
    ss << "  P2P Support: " << support_level_str(p2p_support_) << "\n";
    ss << "  VFIO Module: " << (vfio_module_loaded_ ? "Loaded" : "Not Loaded") << "\n";
    ss << "  P2P Module: " << (p2p_module_loaded_ ? "Loaded" : "Not Loaded") << "\n";
    ss << "  ACS Override: " << (acs_override_ ? "Enabled" : "Disabled") << "\n";
    ss << "  Admin Privileges: " << (has_admin_ ? "Yes" : "No");

    return ss.str();
}

void HostFeature::print(bool verbose) const {
    printf("=== Host System ===\n");
    printf("OS: %s\n", os_name_.c_str());
    printf("Kernel: %s\n", kernel_version_.c_str());

    printf("\nIOMMU Status:\n");
    printf("  Hardware: %s\n", iommu_hardware_ ? "Present" : "Not Found");
    if (iommu_hardware_) {
        printf("  Enabled: %s\n", iommu_enabled_ ? "Yes" : "No");
        printf("  Groups: %u\n", iommu_group_count_);
    }

    printf("\nVFIO Status:\n");
    printf("  Support: %s\n", support_level_str(vfio_support_));
    printf("  Module Loaded: %s\n", vfio_module_loaded_ ? "Yes" : "No");
    if (!vfio_module_loaded_ && verbose) {
        printf("  Hint: Run 'sudo modprobe vfio-pci' to load VFIO module\n");
    }

    printf("\nP2P DMA Status:\n");
    printf("  Support: %s\n", support_level_str(p2p_support_));
    printf("  gpu_p2p_nvme Module: %s\n", p2p_module_loaded_ ? "Loaded" : "Not Loaded");
    printf("  ACS Override: %s\n", acs_override_ ? "Enabled" : "Disabled");
    if (!acs_override_ && verbose) {
        printf("  Hint: Add 'pci=noacs' to kernel cmdline if P2P fails\n");
    }

    printf("\nPermissions:\n");
    printf("  Running as root: %s\n", has_admin_ ? "Yes" : "No");
    if (!has_admin_ && verbose) {
        printf("  Note: Some features require root privileges\n");
    }

    printf("\n");
}

const HostFeature& get_host_features() {
    static HostFeature instance;
    return instance;
}
