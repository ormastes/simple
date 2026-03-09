/**
 * @file nvme_feature.cpp
 * @brief NVMe feature detection implementation
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "nvme_feature.h"
#include <cstdio>
#include <cstring>
#include <sstream>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <linux/nvme_ioctl.h>

NvmeFeature::NvmeFeature(const string& device_path) : device_path_(device_path) {
    detect_features();
    if (available_) {
        detect_vfio_status();
        detect_shadow_doorbell();
        detect_filesystem_status();  // SAFETY: Check for filesystems/partitions
        detect_boot_device_status();  // SAFETY: Check if boot device
    }
}

void NvmeFeature::detect_features() {
    // Check if device exists
    struct stat st;
    if (stat(device_path_.c_str(), &st) != 0) {
        available_ = false;
        return;
    }

    // Try to open device
    int fd = open(device_path_.c_str(), O_RDONLY);
    if (fd < 0) {
        available_ = false;
        return;
    }

    available_ = true;

    // Read Identify Controller data
    read_identify_controller();

    // Get PCI bus ID from sysfs
    // /dev/nvme0 -> /sys/class/nvme/nvme0/device -> ../../0000:08:00.0
    string sysfs_path = "/sys/class/nvme/" +
                        device_path_.substr(device_path_.rfind('/') + 1) +
                        "/device";

    char resolved_path[PATH_MAX];
    if (realpath(sysfs_path.c_str(), resolved_path)) {
        // Extract PCI bus ID from path
        string path_str(resolved_path);
        size_t pos = path_str.rfind('/');
        if (pos != string::npos) {
            pci_bus_id_ = path_str.substr(pos + 1);
        }
    }

    // Get namespace count from sysfs
    string ns_path = "/sys/class/nvme/" +
                     device_path_.substr(device_path_.rfind('/') + 1);

    DIR* dir = opendir(ns_path.c_str());
    if (dir) {
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            // Count nvme0n1, nvme0n2, etc.
            if (strstr(entry->d_name, "nvme") && strchr(entry->d_name, 'n')) {
                num_namespaces_++;
            }
        }
        closedir(dir);
    }

    // Get capacity from first namespace
    if (num_namespaces_ > 0) {
        string cap_path = ns_path + "/" +
                          device_path_.substr(device_path_.rfind('/') + 1) +
                          "n1/size";
        FILE* f = fopen(cap_path.c_str(), "r");
        if (f) {
            uint64_t sectors;
            if (fscanf(f, "%lu", &sectors) == 1) {
                capacity_bytes_ = sectors * 512;  // Kernel reports in 512-byte sectors
            }
            fclose(f);
        }
    }

    close(fd);
}

void NvmeFeature::read_identify_controller() {
    int fd = open(device_path_.c_str(), O_RDONLY);
    if (fd < 0) return;

    // Use NVMe admin command to get Identify Controller
    struct nvme_admin_cmd cmd = {};
    uint8_t id_ctrl[4096] __attribute__((aligned(4096))) = {};

    cmd.opcode = 0x06;  // Identify
    cmd.nsid = 0;       // Controller
    cmd.addr = (uint64_t)id_ctrl;
    cmd.data_len = sizeof(id_ctrl);
    cmd.cdw10 = 1;      // CNS=1 (Identify Controller)

    if (ioctl(fd, NVME_IOCTL_ADMIN_CMD, &cmd) == 0) {
        // Parse Identify Controller data structure

        // Model name (bytes 24-63)
        char model[41] = {};
        memcpy(model, &id_ctrl[24], 40);
        // Trim trailing spaces
        for (int i = 39; i >= 0; i--) {
            if (model[i] == ' ') model[i] = '\0';
            else break;
        }
        model_ = model;

        // Firmware revision (bytes 64-71)
        char fw[9] = {};
        memcpy(fw, &id_ctrl[64], 8);
        for (int i = 7; i >= 0; i--) {
            if (fw[i] == ' ') fw[i] = '\0';
            else break;
        }
        firmware_version_ = fw;

        // Max I/O queues (word 34-35, 0-based)
        uint16_t mqes = *(uint16_t*)&id_ctrl[0];  // MQES (Maximum Queue Entries Supported)
        max_queue_depth_ = mqes + 1;

        // Number of queues supported (bytes 514-515, 516-517)
        uint16_t ncqa = *(uint16_t*)&id_ctrl[514];  // NCQA (Admin)
        uint16_t ncsq = *(uint16_t*)&id_ctrl[516];  // Number of SQ
        max_io_queues_ = ncsq;
    }

    close(fd);
}

void NvmeFeature::detect_vfio_status() {
    if (pci_bus_id_.empty()) return;

    // Check if VFIO-PCI driver is bound
    string driver_path = "/sys/bus/pci/devices/" + pci_bus_id_ + "/driver";
    char driver_link[PATH_MAX];
    ssize_t len = readlink(driver_path.c_str(), driver_link, sizeof(driver_link) - 1);

    if (len > 0) {
        driver_link[len] = '\0';
        if (strstr(driver_link, "vfio-pci")) {
            vfio_bound_ = true;
            p2p_support_ = SupportLevel::HARDWARE_ONLY;

            // Check if kernel module is loaded
            int fd = open("/dev/gpu_p2p_nvme", O_RDONLY);
            if (fd >= 0) {
                p2p_support_ = SupportLevel::FULL;
                close(fd);
            }
        }
    }
}

void NvmeFeature::detect_shadow_doorbell() {
    // Shadow doorbell (DBC) support detection
    // Checks OACS (Optional Admin Command Support) bit 8 for DBC capability

    int fd = open(device_path_.c_str(), O_RDONLY);
    if (fd < 0) return;

    // Get Identify Controller data structure
    struct nvme_admin_cmd cmd = {};
    uint8_t id_ctrl[4096] __attribute__((aligned(4096))) = {};

    cmd.opcode = 0x06;  // Identify
    cmd.nsid = 0;       // Controller
    cmd.addr = (uint64_t)id_ctrl;
    cmd.data_len = sizeof(id_ctrl);
    cmd.cdw10 = 1;      // CNS=1 (Identify Controller)

    if (ioctl(fd, NVME_IOCTL_ADMIN_CMD, &cmd) == 0) {
        // Get NVMe version (bytes 80-83) for informational purposes
        uint32_t vs = *(uint32_t*)&id_ctrl[80];
        uint8_t major = (vs >> 16) & 0xFFFF;
        uint8_t minor = (vs >> 8) & 0xFF;

        // CRITICAL: Check OACS (Optional Admin Command Support) at byte 256
        // Bit 8 indicates Doorbell Buffer Config (DBC) command support
        uint16_t oacs = *(uint16_t*)&id_ctrl[256];
        oacs_ = oacs;  // Store for later queries
        nvme_version_major_ = major;
        nvme_version_minor_ = minor;
        bool dbc_supported = (oacs & (1 << 8)) != 0;
        bool known_pm9a1_family = (model_.find("PM9A1") != string::npos) ||
                                  (model_.find("PM9A3") != string::npos) ||
                                  (model_.find("980PRO") != string::npos);

        if (dbc_supported) {
            // Hardware DBC is supported
            shadow_doorbell_support_ = SupportLevel::FULL;
        } else if (known_pm9a1_family) {
            // PM9A1 firmware may hide bit 8 even though hardware supports shadow DB
            shadow_doorbell_support_ = SupportLevel::FULL;
            fprintf(stderr,
                    "[NVMe] %s: Assuming DBC supported for %s family (OACS=0x%04x, bit 8 clear)\n",
                    device_path_.c_str(), model_.c_str(), oacs);
        } else {
            // DBC command not supported by this controller
            shadow_doorbell_support_ = SupportLevel::NOT_SUPPORTED;
        }

        // Log detection result for debugging
        if (dbc_supported) {
            fprintf(stderr, "[NVMe] %s: DBC supported (NVMe %d.%d, OACS=0x%04x)\n",
                    device_path_.c_str(), major, minor, oacs);
        } else {
            fprintf(stderr, "[NVMe] %s: DBC NOT supported (NVMe %d.%d, OACS=0x%04x)\n",
                    device_path_.c_str(), major, minor, oacs);
        }
    }

    close(fd);
}

uint32_t NvmeFeature::get_lba_size(uint32_t nsid) const {
    if (!available_ || nsid < 1 || nsid > num_namespaces_) {
        return lba_size_;
    }

    // Read from sysfs
    string lba_path = "/sys/class/nvme/" +
                      device_path_.substr(device_path_.rfind('/') + 1) + "/" +
                      device_path_.substr(device_path_.rfind('/') + 1) +
                      "n" + std::to_string(nsid) + "/queue/logical_block_size";

    FILE* f = fopen(lba_path.c_str(), "r");
    if (f) {
        uint32_t size;
        if (fscanf(f, "%u", &size) == 1) {
            fclose(f);
            return size;
        }
        fclose(f);
    }

    return lba_size_;
}

string NvmeFeature::get_name() const {
    if (!available_) {
        return device_path_ + " (unavailable)";
    }
    if (model_.empty()) {
        return device_path_;
    }
    return model_ + " (" + device_path_ + ")";
}

string NvmeFeature::get_description() const {
    stringstream ss;

    if (!available_) {
        ss << device_path_ << ": Not available";
        return ss.str();
    }

    ss << device_path_ << ": " << model_ << "\n";
    ss << "  Firmware: " << firmware_version_ << "\n";
    ss << "  PCI Bus ID: " << pci_bus_id_ << "\n";
    ss << "  Capacity: " << (capacity_bytes_ / (1024.0 * 1024 * 1024)) << " GB\n";
    ss << "  Namespaces: " << num_namespaces_ << "\n";
    ss << "  Max I/O Queues: " << max_io_queues_ << "\n";
    ss << "  Max Queue Depth: " << max_queue_depth_ << "\n";
    ss << "  Shadow Doorbell: " << support_level_str(shadow_doorbell_support_) << "\n";
    ss << "  P2P Support: " << support_level_str(p2p_support_) << "\n";
    ss << "  VFIO Bound: " << (vfio_bound_ ? "Yes" : "No");

    return ss.str();
}

void NvmeFeature::print(bool verbose) const {
    printf("=== NVMe Device %s ===\n", device_path_.c_str());

    if (!available_) {
        printf("Status: Not available\n");
        return;
    }

    printf("Model: %s\n", model_.c_str());
    printf("Firmware: %s\n", firmware_version_.c_str());
    printf("Capacity: %.2f GB\n", capacity_bytes_ / (1024.0 * 1024 * 1024));
    printf("Namespaces: %u\n", num_namespaces_);

    if (verbose) {
        printf("PCI Bus ID: %s\n", pci_bus_id_.c_str());
        printf("Max I/O Queues: %u\n", max_io_queues_);
        printf("Max Queue Depth: %u\n", max_queue_depth_);
        printf("LBA Size: %u bytes\n", lba_size_);
        printf("VFIO Bound: %s\n", vfio_bound_ ? "Yes" : "No");
    }

    printf("Shadow Doorbell: %s\n", support_level_str(shadow_doorbell_support_));
    printf("P2P Support: %s\n", support_level_str(p2p_support_));

    // SAFETY STATUS
    printf("\n");
    printf("=== SAFETY STATUS ===\n");
    printf("Boot Device: %s %s\n",
           is_boot_device_ ? "YES" : "NO",
           is_boot_device_ ? "(CRITICAL: DO NOT USE FOR TESTING!)" : "");
    printf("Filesystem/Partitions: %s %s\n",
           has_filesystem_ ? "YES" : "NO",
           has_filesystem_ ? "(WARNING: Has data - do not use for testing!)" : "");

    if (!is_boot_device_ && !has_filesystem_) {
        printf("Test Safety: SAFE (can be used for testing)\n");
    } else {
        printf("Test Safety: UNSAFE (NEVER use for testing)\n");
    }

    printf("\n");
}

// ============================================================================
// SAFETY: Filesystem and Boot Device Detection
// ============================================================================

void NvmeFeature::detect_filesystem_status() {
    has_filesystem_ = false;

    // Check 1: Is any partition from this device mounted?
    FILE* mounts = fopen("/proc/mounts", "r");
    if (mounts) {
        char line[1024];
        string dev_basename = device_path_.substr(device_path_.rfind('/') + 1);

        while (fgets(line, sizeof(line), mounts)) {
            // Check if line starts with our device (e.g., /dev/nvme0n1)
            if (strstr(line, dev_basename.c_str()) == line) {
                has_filesystem_ = true;
                fclose(mounts);
                return;
            }
        }
        fclose(mounts);
    }

    // Check 2: Does device have partition table?
    // Use blkid to check for partition table or filesystem signature
    string cmd = "blkid " + device_path_ + " 2>/dev/null";
    FILE* pipe = popen(cmd.c_str(), "r");
    if (pipe) {
        char buffer[512];
        if (fgets(buffer, sizeof(buffer), pipe)) {
            // blkid output exists = has filesystem or partition table
            has_filesystem_ = true;
        }
        pclose(pipe);
    }

    // Check 3: Check for namespace partitions (nvme0n1, nvme0n2, etc.)
    string dev_basename = device_path_.substr(device_path_.rfind('/') + 1);
    DIR* dir = opendir("/dev");
    if (dir) {
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            // Look for nvme0n* pattern
            if (strncmp(entry->d_name, dev_basename.c_str(), dev_basename.length()) == 0 &&
                strlen(entry->d_name) > dev_basename.length() &&
                entry->d_name[dev_basename.length()] == 'n') {

                // Found namespace - check if it has filesystem
                string ns_path = "/dev/" + string(entry->d_name);
                string ns_cmd = "blkid " + ns_path + " 2>/dev/null";
                FILE* ns_pipe = popen(ns_cmd.c_str(), "r");
                if (ns_pipe) {
                    char ns_buf[512];
                    if (fgets(ns_buf, sizeof(ns_buf), ns_pipe)) {
                        has_filesystem_ = true;
                        pclose(ns_pipe);
                        closedir(dir);
                        return;
                    }
                    pclose(ns_pipe);
                }
            }
        }
        closedir(dir);
    }
}

void NvmeFeature::detect_boot_device_status() {
    is_boot_device_ = false;

    // Check 1: Is root filesystem on this device?
    FILE* mounts = fopen("/proc/mounts", "r");
    if (mounts) {
        char line[1024];
        string dev_basename = device_path_.substr(device_path_.rfind('/') + 1);

        while (fgets(line, sizeof(line), mounts)) {
            // Check if root (/) or /boot is mounted from this device
            if (strstr(line, dev_basename.c_str()) == line) {
                // Parse mount point (2nd field)
                char device[256], mountpoint[256];
                if (sscanf(line, "%s %s", device, mountpoint) == 2) {
                    if (strcmp(mountpoint, "/") == 0 || strcmp(mountpoint, "/boot") == 0) {
                        is_boot_device_ = true;
                        fclose(mounts);
                        return;
                    }
                }
            }
        }
        fclose(mounts);
    }

    // Check 2: Parse kernel command line for root device
    FILE* cmdline = fopen("/proc/cmdline", "r");
    if (cmdline) {
        char line[2048];
        if (fgets(line, sizeof(line), cmdline)) {
            string dev_basename = device_path_.substr(device_path_.rfind('/') + 1);

            // Look for root=/dev/nvme0... or root=UUID/PARTUUID pointing to this device
            if (strstr(line, dev_basename.c_str())) {
                is_boot_device_ = true;
            }

            // Also check for UUID/PARTUUID
            if (strstr(line, "root=UUID=") || strstr(line, "root=PARTUUID=")) {
                // Would need to resolve UUID to device, for now flag as potentially boot
                // (Conservative: if we find UUID and this device has filesystem, be cautious)
                if (has_filesystem_) {
                    // Too risky - mark as boot device to be safe
                    is_boot_device_ = true;
                }
            }
        }
        fclose(cmdline);
    }
}

bool NvmeFeature::is_lba_range_safe(uint64_t start_lba, uint64_t num_lbas,
                                   uint32_t min_safe_offset_gb) const {
    // Check 1: CRITICAL - Never allow if device has filesystem or is boot device
    if (has_filesystem_ || is_boot_device_) {
        return false;  // ABSOLUTELY NOT SAFE
    }

    // Check 2: Range must be within capacity
    uint64_t max_lba = capacity_bytes_ / lba_size_;
    if (start_lba + num_lbas > max_lba) {
        return false;  // Beyond capacity
    }

    // Check 3: Must be beyond minimum safe offset
    uint64_t min_safe_lba = (static_cast<uint64_t>(min_safe_offset_gb) * 1024 * 1024 * 1024) / lba_size_;
    if (start_lba < min_safe_lba) {
        return false;  // Too close to beginning (potential metadata area)
    }

    return true;
}

std::vector<NvmeFeature> get_all_nvme_devices() {
    std::vector<NvmeFeature> devices;

    // Scan /dev for nvme* devices (nvme0, nvme1, etc.)
    DIR* dir = opendir("/dev");
    if (!dir) return devices;

    struct dirent* entry;
    while ((entry = readdir(dir)) != nullptr) {
        if (strncmp(entry->d_name, "nvme", 4) == 0) {
            // Skip namespace devices (nvme0n1, nvme0n2)
            if (strchr(entry->d_name, 'n') == nullptr) {
                string dev_path = "/dev/" + string(entry->d_name);
                devices.emplace_back(dev_path);
            }
        }
    }

    closedir(dir);
    return devices;
}
