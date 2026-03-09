/**
 * @file gpu_feature.cpp
 * @brief GPU feature detection implementation
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "gpu_feature.h"
#include <cstdio>
#include <cstring>
#include <sstream>
#include <fcntl.h>
#include <unistd.h>

GpuFeature::GpuFeature(int device_id) : device_id_(device_id) {
    detect_features();
    if (cuda_available_) {
        detect_p2p_support();
    }
}

void GpuFeature::detect_features() {
    // Check CUDA availability using cuda_utils.h helper
    int device_count = get_device_count();

    if (device_count == 0) {
        cuda_available_ = false;
        return;
    }

    if (device_id_ >= device_count) {
        cuda_available_ = false;
        return;
    }

    // Get device properties using cuda_utils.h helper
    if (!get_device_props(props_, device_id_)) {
        cuda_available_ = false;
        return;
    }

    cuda_available_ = true;
    device_name_ = props_.name;
    compute_major_ = props_.major;
    compute_minor_ = props_.minor;
    total_memory_ = props_.totalGlobalMem;
    unified_memory_ = props_.unifiedAddressing;

    // Get PCI bus ID
    char pci_bus_id[64] = {0};
    cudaError_t err = cudaDeviceGetPCIBusId(pci_bus_id, sizeof(pci_bus_id), device_id_);
    if (err == cudaSuccess) {
        pci_bus_id_ = pci_bus_id;
    }

    // Try to get BAR1 size from sysfs
    if (!pci_bus_id_.empty()) {
        // Convert PCI bus ID to sysfs path
        // e.g., "0000:01:00.0" -> "/sys/bus/pci/devices/0000:01:00.0/resource"
        stringstream ss;
        ss << "/sys/bus/pci/devices/" << pci_bus_id_ << "/resource";

        int fd = open(ss.str().c_str(), O_RDONLY);
        if (fd >= 0) {
            char buf[1024];
            ssize_t len = read(fd, buf, sizeof(buf) - 1);
            if (len > 0) {
                buf[len] = '\0';
                // Parse resource file (line 1 is BAR1)
                // Format: start end flags (hex values)
                char* line = buf;
                char* next_line = strchr(line, '\n');
                if (next_line) {
                    next_line++;  // Skip BAR0
                    char* bar1_line = next_line;
                    next_line = strchr(bar1_line, '\n');
                    if (next_line) {
                        *next_line = '\0';
                        uint64_t start, end, flags;
                        if (sscanf(bar1_line, "0x%lx 0x%lx 0x%lx", &start, &end, &flags) == 3) {
                            bar1_size_ = end - start + 1;
                        }
                    }
                }
            }
            close(fd);
        }
    }
}

void GpuFeature::detect_p2p_support() {
    // Check if GPU can access NVMe via P2P
    // Requirements:
    // 1. BAR1 size >= 256MB (recommended for good performance)
    // 2. Compute capability >= 3.5 (Kepler+)
    // 3. Unified addressing support
    // 4. gpu_p2p_nvme kernel module (checked separately)

    if (!unified_memory_) {
        nvme_p2p_support_ = SupportLevel::NOT_SUPPORTED;
        return;
    }

    if (compute_major_ < 3 || (compute_major_ == 3 && compute_minor_ < 5)) {
        nvme_p2p_support_ = SupportLevel::NOT_SUPPORTED;
        return;
    }

    // Check BAR1 size
    if (bar1_size_ == 0) {
        // Could not determine BAR1 size - assume hardware support
        nvme_p2p_support_ = SupportLevel::HARDWARE_ONLY;
        return;
    }

    const size_t recommended_bar1 = 256 * 1024 * 1024;  // 256MB
    if (bar1_size_ < recommended_bar1) {
        nvme_p2p_support_ = SupportLevel::PARTIAL;
    } else {
        // Hardware supports it, but need kernel module for FULL
        nvme_p2p_support_ = SupportLevel::HARDWARE_ONLY;
    }

    // Check if kernel module is loaded
    int fd = open("/dev/gpu_p2p_nvme", O_RDONLY);
    if (fd >= 0) {
        nvme_p2p_support_ = SupportLevel::FULL;
        close(fd);
    }
}

bool GpuFeature::has_p2p_to_gpu(int peer_device_id) const {
    if (!cuda_available_) return false;

    int can_access = 0;
    cudaError_t err = cudaDeviceCanAccessPeer(&can_access, device_id_, peer_device_id);
    return (err == cudaSuccess && can_access);
}

string GpuFeature::get_name() const {
    if (!cuda_available_) {
        return "GPU " + std::to_string(device_id_) + " (unavailable)";
    }
    return device_name_;
}

string GpuFeature::get_description() const {
    stringstream ss;

    if (!cuda_available_) {
        ss << "GPU " << device_id_ << ": Not available";
        return ss.str();
    }

    ss << "GPU " << device_id_ << ": " << device_name_ << "\n";
    ss << "  Compute Capability: " << compute_major_ << "." << compute_minor_ << "\n";
    ss << "  Total Memory: " << (total_memory_ / (1024.0 * 1024 * 1024)) << " GB\n";
    ss << "  PCI Bus ID: " << pci_bus_id_ << "\n";

    if (bar1_size_ > 0) {
        ss << "  BAR1 Size: " << (bar1_size_ / (1024 * 1024)) << " MB\n";
    }

    ss << "  Unified Memory: " << (unified_memory_ ? "Yes" : "No") << "\n";
    ss << "  NVMe P2P Support: " << support_level_str(nvme_p2p_support_);

    return ss.str();
}

void GpuFeature::print(bool verbose) const {
    printf("=== GPU %d ===\n", device_id_);

    if (!cuda_available_) {
        printf("Status: Not available\n");
        return;
    }

    printf("Name: %s\n", device_name_.c_str());
    printf("Compute Capability: %d.%d\n", compute_major_, compute_minor_);
    printf("Total Memory: %.2f GB\n", total_memory_ / (1024.0 * 1024 * 1024));

    if (verbose) {
        printf("PCI Bus ID: %s\n", pci_bus_id_.c_str());
        if (bar1_size_ > 0) {
            printf("BAR1 Size: %zu MB\n", bar1_size_ / (1024 * 1024));
        }
        printf("Multiprocessors: %d\n", props_.multiProcessorCount);
        printf("Max Threads per Block: %d\n", props_.maxThreadsPerBlock);
        printf("Warp Size: %d\n", props_.warpSize);
        printf("Unified Memory: %s\n", unified_memory_ ? "Yes" : "No");
    }

    printf("NVMe P2P Support: %s\n", support_level_str(nvme_p2p_support_));
    printf("\n");
}

std::vector<GpuFeature> get_all_gpus() {
    std::vector<GpuFeature> gpus;

    // Use cuda_utils.h helper for cleaner code
    int device_count = get_device_count();

    if (device_count == 0) {
        return gpus;
    }

    for (int i = 0; i < device_count; i++) {
        gpus.emplace_back(i);
    }

    return gpus;
}
