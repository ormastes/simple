/**
 * @file device_info_demo.cpp
 * @brief Demonstration of device feature detection system
 *
 * Shows how to use the device detection API to enumerate
 * GPUs, NVMe devices, and check P2P readiness.
 *
 * Usage:
 *   ./device_info_demo           # Brief summary
 *   ./device_info_demo -v        # Verbose details
 *   ./device_info_demo --report  # Full compatibility report
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-09
 */

#include "device/device_detector.h"
#include <cstdio>
#include <cstring>

void print_usage(const char* prog) {
    printf("Usage: %s [options]\n", prog);
    printf("\nOptions:\n");
    printf("  (none)     Show brief summary\n");
    printf("  -v         Show verbose device details\n");
    printf("  --report   Show full compatibility report\n");
    printf("  --help     Show this help\n");
}

int main(int argc, char* argv[]) {
    bool verbose = false;
    bool show_report = false;

    // Parse arguments
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0 || strcmp(argv[i], "--verbose") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "--report") == 0) {
            show_report = true;
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            printf("Unknown option: %s\n", argv[i]);
            print_usage(argv[0]);
            return 1;
        }
    }

    printf("Detecting devices...\n\n");

    // Detect all devices
    auto features = SystemFeatures::detect_all();

    if (show_report) {
        // Print full compatibility report
        features.print_all(verbose);
        print_compatibility_report(features);
    } else if (verbose) {
        // Print detailed information
        features.print_all(true);
    } else {
        // Print brief summary
        printf("%s\n", features.get_summary().c_str());
    }

    // Example: Find specific devices
    printf("\n=== Usage Examples ===\n");

    // Find GPU 0
    const auto* gpu0 = features.find_gpu(0);
    if (gpu0) {
        printf("\nGPU 0 Details:\n");
        printf("  Name: %s\n", gpu0->get_name().c_str());
        printf("  Compute: %d.%d\n", gpu0->get_compute_major(), gpu0->get_compute_minor());
        printf("  Memory: %.2f GB\n", gpu0->get_total_memory() / (1024.0 * 1024 * 1024));
        printf("  P2P to NVMe: %s\n", support_level_str(gpu0->get_nvme_p2p_support()));
    }

    // Find first NVMe device
    if (!features.nvme_devs.empty()) {
        const auto& nvme0 = features.nvme_devs[0];
        printf("\nFirst NVMe Device:\n");
        printf("  Path: %s\n", nvme0.get_device_path().c_str());
        printf("  Model: %s\n", nvme0.get_model().c_str());
        printf("  Capacity: %.2f GB\n", nvme0.get_capacity_bytes() / (1024.0 * 1024 * 1024));
        printf("  Namespaces: %u\n", nvme0.get_num_namespaces());
        printf("  P2P Support: %s\n", support_level_str(nvme0.get_p2p_support()));
    }

    // Show P2P-capable devices
    auto p2p_gpus = features.get_p2p_capable_gpus();
    auto p2p_nvme = features.get_p2p_capable_nvme();

    printf("\nP2P-Capable Devices:\n");
    printf("  GPUs: %zu of %zu\n", p2p_gpus.size(), features.gpus.size());
    for (auto idx : p2p_gpus) {
        printf("    - GPU %d: %s\n", features.gpus[idx].get_device_id(),
               features.gpus[idx].get_name().c_str());
    }

    printf("  NVMe: %zu of %zu\n", p2p_nvme.size(), features.nvme_devs.size());
    for (auto idx : p2p_nvme) {
        printf("    - %s\n", features.nvme_devs[idx].get_device_path().c_str());
    }

    // Exit code based on P2P readiness
    if (features.is_p2p_ready()) {
        printf("\n✓ System is ready for GPU-NVMe P2P!\n");
        return 0;
    } else {
        printf("\n✗ System is NOT ready for GPU-NVMe P2P\n");
        printf("  Run with --report for details on how to fix\n");
        return 1;
    }
}
