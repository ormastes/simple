/**
 * @file device_detector.cpp
 * @brief Device detection implementation
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "device_detector.h"
#include <cstdio>
#include <sstream>
#include <algorithm>
#include <cstring>
#include <optional>

bool SystemFeatures::is_p2p_ready() const {
    // Check host requirements
    if (host.get_vfio_support() != SupportLevel::FULL) {
        return false;
    }

    if (host.get_p2p_support() != SupportLevel::FULL) {
        return false;
    }

    // Check for at least one P2P-capable GPU
    bool has_p2p_gpu = false;
    for (const auto& gpu : gpus) {
        if (gpu.get_nvme_p2p_support() == SupportLevel::FULL) {
            has_p2p_gpu = true;
            break;
        }
    }

    if (!has_p2p_gpu) {
        return false;
    }

    // Check for at least one P2P-capable NVMe device
    bool has_p2p_nvme = false;
    for (const auto& nvme : nvme_devs) {
        if (nvme.get_p2p_support() == SupportLevel::FULL) {
            has_p2p_nvme = true;
            break;
        }
    }

    return has_p2p_nvme;
}

string SystemFeatures::get_summary() const {
    stringstream ss;

    ss << "=== System Feature Summary ===\n\n";

    ss << "Host: " << host.get_os_name() << " (Kernel " << host.get_kernel_version() << ")\n";
    ss << "  VFIO: " << support_level_str(host.get_vfio_support()) << "\n";
    ss << "  P2P: " << support_level_str(host.get_p2p_support()) << "\n\n";

    ss << "GPUs: " << gpus.size() << " detected\n";
    for (size_t i = 0; i < gpus.size(); i++) {
        const auto& gpu = gpus[i];
        ss << "  [" << i << "] " << gpu.get_name();
        if (gpu.get_nvme_p2p_support() == SupportLevel::FULL) {
            ss << " (P2P Ready)";
        }
        ss << "\n";
    }
    ss << "\n";

    ss << "NVMe Devices: " << nvme_devs.size() << " detected\n";
    for (size_t i = 0; i < nvme_devs.size(); i++) {
        const auto& nvme = nvme_devs[i];
        ss << "  [" << i << "] " << nvme.get_name();
        if (nvme.get_p2p_support() == SupportLevel::FULL) {
            ss << " (P2P Ready)";
        }
        ss << "\n";
    }
    ss << "\n";

    ss << "P2P Status: " << (is_p2p_ready() ? "Ready" : "Not Ready");

    return ss.str();
}

void SystemFeatures::print_all(bool verbose) const {
    printf("=====================================\n");
    printf("   SYSTEM DEVICE DETECTION REPORT   \n");
    printf("=====================================\n\n");

    host.print(verbose);

    printf("-------------------------------------\n");
    printf("GPUs (%zu detected)\n", gpus.size());
    printf("-------------------------------------\n");
    for (const auto& gpu : gpus) {
        gpu.print(verbose);
    }

    printf("-------------------------------------\n");
    printf("NVMe Devices (%zu detected)\n", nvme_devs.size());
    printf("-------------------------------------\n");
    for (const auto& nvme : nvme_devs) {
        nvme.print(verbose);
    }

    printf("=====================================\n");
    printf("P2P Status: %s\n", is_p2p_ready() ? "Ready ✓" : "Not Ready ✗");
    printf("=====================================\n");
}

const GpuFeature* SystemFeatures::find_gpu(int device_id) const {
    for (const auto& gpu : gpus) {
        if (gpu.get_device_id() == device_id) {
            return &gpu;
        }
    }
    return nullptr;
}

const NvmeFeature* SystemFeatures::find_nvme(const string& device_path) const {
    for (const auto& nvme : nvme_devs) {
        if (nvme.get_device_path() == device_path) {
            return &nvme;
        }
    }
    return nullptr;
}

std::vector<size_t> SystemFeatures::get_p2p_capable_gpus() const {
    std::vector<size_t> result;
    for (size_t i = 0; i < gpus.size(); i++) {
        if (gpus[i].get_nvme_p2p_support() == SupportLevel::FULL) {
            result.push_back(i);
        }
    }
    return result;
}

std::vector<size_t> SystemFeatures::get_p2p_capable_nvme() const {
    std::vector<size_t> result;
    for (size_t i = 0; i < nvme_devs.size(); i++) {
        if (nvme_devs[i].get_p2p_support() == SupportLevel::FULL) {
            result.push_back(i);
        }
    }
    return result;
}

SystemFeatures SystemFeatures::detect_all() {
    SystemFeatures features;

    // Detect host capabilities first
    features.host = get_host_features();

    // Detect GPUs
    features.gpus = get_all_gpus();

    // Detect NVMe devices
    features.nvme_devs = get_all_nvme_devices();

    return features;
}

// SelectedDevices implementation
string SelectedDevices::get_description() const {
    stringstream ss;

    ss << "Selected Devices:\n";

    if (host) {
        ss << "  Host: " << host->get_os_name()
           << " (" << (host->get_total_memory() / (1024.0*1024*1024)) << " GB RAM)\n";
        ss << "    VFIO: " << support_level_str(host->get_vfio_support()) << "\n";
        ss << "    P2P: " << support_level_str(host->get_p2p_support()) << "\n";
    } else {
        ss << "  Host: Not selected\n";
    }

    if (gpu) {
        ss << "  GPU: " << gpu->get_name()
           << " (" << (gpu->get_total_memory() / (1024.0*1024*1024)) << " GB)\n";
        ss << "    Compute: " << gpu->get_compute_major() << "." << gpu->get_compute_minor() << "\n";
        ss << "    P2P: " << support_level_str(gpu->get_nvme_p2p_support()) << "\n";
    } else {
        ss << "  GPU: Not selected\n";
    }

    if (nvme) {
        ss << "  NVMe: " << nvme->get_model()
           << " (" << (nvme->get_capacity_bytes() / (1024.0*1024*1024)) << " GB)\n";
        ss << "    Path: " << nvme->get_device_path() << "\n";
        ss << "    Shadow DB: " << support_level_str(nvme->get_shadow_doorbell_support()) << "\n";
        ss << "    P2P: " << support_level_str(nvme->get_p2p_support()) << "\n";
    } else {
        ss << "  NVMe: Not selected\n";
    }

    return ss.str();
}

void SelectedDevices::print() const {
    printf("%s", get_description().c_str());
}

// SystemFeatures device selection implementation
bool SystemFeatures::gpu_matches(const GpuFeature& gpu, const DeviceRequirements& req) const {
    // If specific GPU PCI ID requested, only match that device
    if (!req.specific_gpu_pci_id.empty()) {
        if (gpu.get_pci_bus_id() != req.specific_gpu_pci_id) {
            return false;  // Not the requested device
        }
    }

    if (req.require_cuda && !gpu.has_cuda()) {
        return false;
    }

    if (req.require_gpu_pinned_memory && !gpu.has_unified_memory()) {
        return false;
    }

    if (req.require_gpu_p2p && gpu.get_nvme_p2p_support() != SupportLevel::FULL) {
        return false;
    }

    if (req.min_gpu_memory > 0 && gpu.get_total_memory() < req.min_gpu_memory) {
        return false;
    }

    return true;
}

bool SystemFeatures::nvme_matches(const NvmeFeature& nvme, const DeviceRequirements& req) const {
    if (!nvme.is_available()) {
        return false;
    }

    // CRITICAL SAFETY: Never use boot device
    if (nvme.is_boot_device()) {
        return false;
    }

    // SAFETY: Never use device with filesystem or partitions
    if (nvme.is_filesystem_bound()) {
        return false;
    }

    // SAFETY: Validate PCI BDF
    std::string bdf = nvme.get_pci_bus_id();
    if (bdf.empty() || bdf == "") {  // Empty BDF is invalid
        return false;
    }

    // If specific BDF requested, only match that device
    if (!req.specific_nvme_bdf.empty()) {
        if (bdf != req.specific_nvme_bdf) {
            return false;  // Not the requested device
        }
    }

    // Additional safety check for VFIO binding would go here
    // For now, we'll rely on the feature checks below

    if (req.require_nvme_vfio && !nvme.has_vfio_binding()) {
        return false;
    }

    if (req.require_shadow_doorbell) {
        auto level = nvme.get_shadow_doorbell_support();
        if (level != SupportLevel::FULL && level != SupportLevel::PARTIAL) {
            return false;
        }

        if (req.require_full_shadow_doorbell && level != SupportLevel::FULL) {
            return false;
        }
    }

    if (req.require_nvme_p2p && nvme.get_p2p_support() != SupportLevel::FULL) {
        return false;
    }

    if (req.min_nvme_capacity > 0 && nvme.get_capacity_bytes() < req.min_nvme_capacity) {
        return false;
    }

    return true;
}

bool SystemFeatures::host_matches(const HostFeature& host_feat, const DeviceRequirements& req) const {
    if (req.require_vfio && host_feat.get_vfio_support() != SupportLevel::FULL) {
        return false;
    }

    if (req.require_host_p2p && host_feat.get_p2p_support() != SupportLevel::FULL) {
        return false;
    }

    if (req.require_iommu && !host_feat.has_iommu_enabled()) {
        return false;
    }

    if (req.min_host_memory > 0 && host_feat.get_total_memory() < req.min_host_memory) {
        return false;
    }

    return true;
}

std::vector<size_t> SystemFeatures::get_matching_gpus(const DeviceRequirements& req) const {
    std::vector<size_t> matches;

    // Find all matching GPUs
    for (size_t i = 0; i < gpus.size(); i++) {
        if (gpu_matches(gpus[i], req)) {
            matches.push_back(i);
        }
    }

    // Sort by memory (descending)
    std::sort(matches.begin(), matches.end(),
        [this](size_t a, size_t b) {
            return gpus[a].get_total_memory() >
                   gpus[b].get_total_memory();
        });

    return matches;
}

std::vector<size_t> SystemFeatures::get_matching_nvme(const DeviceRequirements& req) const {
    std::vector<size_t> safe_matches;

    auto capacity_desc = [this](size_t a, size_t b) {
        return nvme_devs[a].get_capacity_bytes() >
               nvme_devs[b].get_capacity_bytes();
    };

    for (size_t i = 0; i < nvme_devs.size(); i++) {
        if (!nvme_matches(nvme_devs[i], req)) {
            continue;
        }
        if (nvme_devs[i].is_os_live()) {
            continue;  // Never select OS-owned devices
        }
        safe_matches.push_back(i);
    }

    // Prioritize DBC-capable NVMe (shadow doorbell support) first, fall back to capacity
    std::sort(safe_matches.begin(), safe_matches.end(), [this](size_t a, size_t b) {
        bool a_dbc = nvme_devs[a].get_shadow_doorbell_support() == SupportLevel::FULL;
        bool b_dbc = nvme_devs[b].get_shadow_doorbell_support() == SupportLevel::FULL;

        if (a_dbc != b_dbc) {
            return a_dbc && !b_dbc;  // DBC-capable first
        }
        return nvme_devs[a].get_capacity_bytes() > nvme_devs[b].get_capacity_bytes();
    });

    return safe_matches;
}

SelectedDevices SystemFeatures::select_devices(const DeviceRequirements& req, bool enable_log) const {
    SelectedDevices result;

    // Host is always the same (singleton)
    result.host = &host;

    // Check if host meets requirements
    if (!host_matches(host, req)) {
        // Build failure log message
        std::stringstream log;
        log << "Host requirements not met:\n";

        if (req.require_vfio && host.get_vfio_support() != SupportLevel::FULL) {
            log << "  - VFIO required but support level is "
                << support_level_str(host.get_vfio_support())
                << " (need FULL)\n";
        }

        if (req.require_host_p2p && host.get_p2p_support() != SupportLevel::FULL) {
            log << "  - P2P required but support level is "
                << support_level_str(host.get_p2p_support())
                << " (need FULL)\n";
        }

        if (req.require_iommu && !host.has_iommu_enabled()) {
            log << "  - IOMMU required but not enabled\n";
        }

        if (req.min_host_memory > 0 && host.get_total_memory() < req.min_host_memory) {
            char buf[256];
            snprintf(buf, sizeof(buf), "  - Minimum host memory: %lu GB, available: %.2f GB\n",
                    req.min_host_memory / (1024UL*1024*1024),
                    host.get_total_memory() / (1024.0*1024*1024));
            log << buf;
        }

        result.host_log = log.str();

        // Optionally print to stderr
        if (enable_log) {
            fprintf(stderr, "[SystemFeatures] %s", result.host_log.c_str());
        }

        result.host = nullptr;
        return result;
    }

    // Host requirements met - empty log
    result.host_log = "";

    // Select best GPU if required
    if (req.require_cuda || req.require_gpu_pinned_memory || req.require_gpu_p2p ||
        req.min_gpu_memory > 0) {

        auto matching_gpus = get_matching_gpus(req);
        if (!matching_gpus.empty()) {
            result.gpu = &gpus[matching_gpus[0]];  // Highest memory
        }
    }

    // Select best NVMe if required
    if (req.require_nvme || req.require_shadow_doorbell || req.require_nvme_p2p ||
        req.min_nvme_capacity > 0) {

        auto matching_nvme = get_matching_nvme(req);
        if (!matching_nvme.empty()) {
            result.nvme = &nvme_devs[matching_nvme[0]];  // Highest capacity
            result.nvme_log = "";  // Success - empty log
        } else {
            // Build failure log message
            std::stringstream log;
            log << "NVMe requirements not met:\n";

            if (nvme_devs.empty()) {
                log << "  - No NVMe devices detected on system\n";
            } else if (!req.specific_nvme_bdf.empty()) {
                // Specific BDF was requested but not found or failed validation
                log << "  - Specific NVMe BDF requested: " << req.specific_nvme_bdf << "\n";

                bool found_device = false;
                for (const auto& nvme : nvme_devs) {
                    if (nvme.get_pci_bus_id() == req.specific_nvme_bdf) {
                        found_device = true;
                        // Device exists but failed validation
                        if (nvme.is_boot_device()) {
                            log << "    * Device is boot device (unsafe to use)\n";
                        }
                        if (nvme.is_filesystem_bound()) {
                            log << "    * Device has mounted filesystems or partitions (unsafe to use)\n";
                        }
                        if (nvme.is_os_live()) {
                            log << "    * Device is OS-managed (unsafe to use)\n";
                        }
                        if (req.require_nvme_vfio && !nvme.has_vfio_binding()) {
                            log << "    * VFIO binding required but device not bound to vfio-pci\n";
                        }
                        break;
                    }
                }

                if (!found_device) {
                    log << "    * Device not detected on system\n";
                    log << "    * Check: ls /sys/bus/pci/devices/" << req.specific_nvme_bdf << "\n";
                }
            } else {
                log << "  - " << nvme_devs.size() << " NVMe device(s) detected but none match requirements:\n";

                if (req.require_nvme_vfio) {
                    size_t vfio_count = 0;
                    for (const auto& nvme : nvme_devs) {
                        if (nvme.has_vfio_binding()) vfio_count++;
                    }
                    log << "    * VFIO binding required: " << vfio_count << "/" << nvme_devs.size() << " bound\n";
                }

                if (req.require_shadow_doorbell) {
                    size_t sdb_count = 0;
                    for (const auto& nvme : nvme_devs) {
                        auto level = nvme.get_shadow_doorbell_support();
                        if (level == SupportLevel::FULL || level == SupportLevel::PARTIAL) sdb_count++;
                    }
                    log << "    * Shadow doorbell required: " << sdb_count << "/" << nvme_devs.size() << " support\n";
                }

                if (req.require_nvme_p2p) {
                    size_t p2p_count = 0;
                    for (const auto& nvme : nvme_devs) {
                        if (nvme.get_p2p_support() == SupportLevel::FULL) p2p_count++;
                    }
                    log << "    * P2P required: " << p2p_count << "/" << nvme_devs.size() << " support FULL\n";
                }

                // Safety exclusions
                size_t boot_count = 0, fs_count = 0, os_live_count = 0;
                for (const auto& nvme : nvme_devs) {
                    if (nvme.is_boot_device()) boot_count++;
                    if (nvme.is_filesystem_bound()) fs_count++;
                    if (nvme.is_os_live()) os_live_count++;
                }
                if (boot_count > 0) log << "    * " << boot_count << " device(s) excluded (boot device)\n";
                if (fs_count > 0) log << "    * " << fs_count << " device(s) excluded (has filesystem/partitions)\n";
                if (os_live_count > 0) log << "    * " << os_live_count << " device(s) excluded (OS-managed)\n";
            }

            result.nvme_log = log.str();

            // Optionally print to stderr
            if (enable_log) {
                fprintf(stderr, "[SystemFeatures] %s", result.nvme_log.c_str());
            }

            result.nvme = nullptr;
        }
    } else {
        // NVMe not required
        result.nvme_log = "";
    }

    return result;
}

void print_compatibility_report(const SystemFeatures& features) {
    printf("\n");
    printf("========================================\n");
    printf("   GPU-NVMe P2P COMPATIBILITY REPORT   \n");
    printf("========================================\n\n");

    // Host requirements
    printf("Host System Requirements:\n");
    printf("  [%s] IOMMU Hardware\n", features.host.has_iommu_hardware() ? "✓" : "✗");
    printf("  [%s] IOMMU Enabled\n", features.host.has_iommu_enabled() ? "✓" : "✗");
    printf("  [%s] VFIO Module Loaded\n", features.host.has_vfio_module() ? "✓" : "✗");
    printf("  [%s] gpu_p2p_nvme Module Loaded\n", features.host.has_p2p_module() ? "✓" : "✗");
    printf("\n");

    // GPU requirements
    auto p2p_gpus = features.get_p2p_capable_gpus();
    printf("GPU Requirements:\n");
    printf("  Found %zu GPU(s), %zu P2P-capable\n", features.gpus.size(), p2p_gpus.size());
    if (p2p_gpus.empty() && !features.gpus.empty()) {
        printf("  Issues:\n");
        for (const auto& gpu : features.gpus) {
            auto level = gpu.get_nvme_p2p_support();
            if (level != SupportLevel::FULL) {
                printf("    - %s: %s\n", gpu.get_name().c_str(), support_level_str(level));
                if (level == SupportLevel::PARTIAL) {
                    printf("      Hint: BAR1 size may be too small (<%dMB)\n", 256);
                }
            }
        }
    }
    printf("\n");

    // NVMe requirements
    auto p2p_nvme = features.get_p2p_capable_nvme();
    printf("NVMe Requirements:\n");
    printf("  Found %zu NVMe device(s), %zu P2P-capable\n",
           features.nvme_devs.size(), p2p_nvme.size());
    if (p2p_nvme.empty() && !features.nvme_devs.empty()) {
        printf("  Issues:\n");
        for (const auto& nvme : features.nvme_devs) {
            auto level = nvme.get_p2p_support();
            if (level != SupportLevel::FULL) {
                printf("    - %s: %s\n", nvme.get_device_path().c_str(),
                       support_level_str(level));
                if (!nvme.has_vfio_binding()) {
                    printf("      Hint: Bind to vfio-pci driver\n");
                    printf("      Command: sudo ./scripts/bind_vfio.sh %s\n",
                           nvme.get_pci_bus_id().c_str());
                }
            }
        }
    }
    printf("\n");

    // Overall status
    printf("========================================\n");
    if (features.is_p2p_ready()) {
        printf("Status: READY FOR P2P ✓\n");
        printf("\nYou can now run GPU-NVMe P2P benchmarks!\n");
    } else {
        printf("Status: NOT READY FOR P2P ✗\n");
        printf("\nAction Items:\n");

        if (!features.host.has_iommu_enabled()) {
            printf("  1. Enable IOMMU in BIOS and kernel:\n");
            printf("     - Add 'intel_iommu=on' (Intel) or 'amd_iommu=on' (AMD) to kernel cmdline\n");
            printf("     - Edit /etc/default/grub and run 'sudo update-grub'\n");
        }

        if (!features.host.has_vfio_module()) {
            printf("  2. Load VFIO modules:\n");
            printf("     sudo modprobe vfio-pci\n");
        }

        if (!features.host.has_p2p_module()) {
            printf("  3. Build and load gpu_p2p_nvme kernel module:\n");
            printf("     cd driver/gpu_p2p_nvme && make && sudo insmod gpu_p2p_nvme.ko\n");
        }

        if (p2p_nvme.empty() && !features.nvme_devs.empty()) {
            printf("  4. Bind NVMe devices to VFIO:\n");
            for (const auto& nvme : features.nvme_devs) {
                if (!nvme.has_vfio_binding()) {
                    printf("     sudo ./scripts/bind_vfio.sh %s\n",
                           nvme.get_pci_bus_id().c_str());
                }
            }
        }
    }

    printf("========================================\n\n");
}
