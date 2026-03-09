/**
 * @file perf_test_helper.h
 * @brief Performance testing helper utilities for NVMe I/O modes
 *
 * Provides common functionality for performance tests including:
 * - Timing utilities
 * - Statistics tracking
 * - Device enumeration
 * - Test configuration
 * - GPU kernel operations
 */

#pragma once

#include <chrono>
#include <vector>
#include <string>
#include <memory>
#include <algorithm>
#include <numeric>
#include <cmath>
#include <iomanip>
#include <sstream>
#include <cuda_runtime.h>
#include <gtest/gtest.h>
#include "device/device_detector.h"
#include "common/patterns/data_patterns.h"

// Include shared performance libraries
#include "perf_stats.h"
#include "perf_timer.h"
#include "gpu_kernels.h"

// CUDA error checking macro
#define CUDA_CHECK(call) do { \
    cudaError_t err = call; \
    if (err != cudaSuccess) { \
        std::cerr << "CUDA error at " << __FILE__ << ":" << __LINE__ \
                  << " - " << cudaGetErrorString(err) << std::endl; \
        exit(1); \
    } \
} while(0)

// Forward declaration for device-aware configuration
struct NvmeDevice;
extern "C" {
    size_t nvme_get_page_size(NvmeDevice* d);
    uint32_t nvme_get_lba_size(NvmeDevice* d);
}

namespace perf_test {

// Default Constants (use device queries when NvmeDevice is available)
// Note: These are fallback values. Prefer nvme_get_page_size() and nvme_get_lba_size()
constexpr size_t DEFAULT_CHUNK_SIZE = 4096;  // 4KB - default, use device page_size when available
constexpr size_t DEFAULT_PAGE_SIZE = 4096;   // Default page size
constexpr uint32_t DEFAULT_LBA_SIZE = 512;   // Default LBA size
constexpr int DEFAULT_ITERATIONS = 1000;
constexpr int WARMUP_ITERATIONS = 10;

/**
 * @brief Get chunk size from device or use default
 * @param device NvmeDevice pointer (can be nullptr)
 * @return Chunk size matching device page size
 */
inline size_t get_chunk_size(NvmeDevice* device) {
    return device ? nvme_get_page_size(device) : DEFAULT_CHUNK_SIZE;
}

/**
 * @brief Get LBA size from device or use default
 * @param device NvmeDevice pointer (can be nullptr)
 * @return LBA size in bytes
 */
inline uint32_t get_lba_size(NvmeDevice* device) {
    return device ? nvme_get_lba_size(device) : DEFAULT_LBA_SIZE;
}

// Use shared types
using PerfStats = perf_common::PerformanceStats;
using Timer = perf_common::Timer;

/**
 * @brief Device configuration for multi-device testing
 */
struct DeviceConfig {
    // NVMe configuration
    std::string nvme_bdf;
    int nvme_nsid;
    int nvme_lba_size;
    uint64_t nvme_slba;
    std::string nvme_type;  // "consumer" or "enterprise"

    // GPU configuration
    int gpu_device_id;
    std::string gpu_name;

    std::string to_string() const {
        std::stringstream ss;
        ss << "NVMe(" << nvme_type << ":" << nvme_bdf << ") + GPU(" << gpu_device_id << ":" << gpu_name << ")";
        return ss.str();
    }
};

/**
 * @brief Enumerate available NVMe and GPU devices for testing
 */
class DeviceEnumerator {
public:
    struct NVMeDevice {
        std::string bdf;
        std::string type;  // "consumer" or "enterprise"
        bool is_os_drive;
    };

    /**
     * @brief Get list of available NVMe devices (excluding OS drive)
     */
    static std::vector<NVMeDevice> enumerate_nvme_devices() {
        std::vector<NVMeDevice> devices;

        // Use real device detection and skip OS/boot drives for safety
        auto features = SystemFeatures::detect_all();
        for (const auto& nvme : features.nvme_devs) {
            if (!nvme.is_available()) {
                continue;
            }
            if (nvme.is_os_live()) {
                // Avoid touching boot/root devices
                continue;
            }

            NVMeDevice entry;
            entry.bdf = nvme.get_pci_bus_id();
            entry.type = (nvme.get_shadow_doorbell_support() == SupportLevel::FULL)
                ? "enterprise"
                : "consumer";
            entry.is_os_drive = nvme.is_os_live();
            devices.push_back(entry);
        }

        // Preserve environment overrides when detection finds nothing
        const char* bdf_env = std::getenv("NVME_BDF");
        if (devices.empty() && bdf_env) {
            devices.push_back({bdf_env, "consumer", false});
        }

        // Add secondary device if configured and not already present
        const char* bdf2_env = std::getenv("NVME_BDF_2");
        if (bdf2_env) {
            const bool already_added = std::any_of(
                devices.begin(), devices.end(),
                [&](const NVMeDevice& dev) { return dev.bdf == bdf2_env; });
            if (!already_added) {
                devices.push_back({bdf2_env, "enterprise", false});
            }
        }

        return devices;
    }

    /**
     * @brief Get list of available CUDA GPUs
     */
    static std::vector<int> enumerate_cuda_devices() {
        std::vector<int> devices;
        int device_count = 0;

        cudaError_t err = cudaGetDeviceCount(&device_count);
        if (err == cudaSuccess) {
            for (int i = 0; i < device_count; ++i) {
                devices.push_back(i);
            }
        }

        return devices;
    }

    /**
     * @brief Generate all device combinations for testing
     */
    static std::vector<DeviceConfig> generate_test_matrix() {
        std::vector<DeviceConfig> configs;

        auto nvme_devices = enumerate_nvme_devices();
        auto gpu_devices = enumerate_cuda_devices();

        for (const auto& nvme : nvme_devices) {
            for (const auto& gpu_id : gpu_devices) {
                DeviceConfig config;

                // NVMe configuration
                config.nvme_bdf = nvme.bdf;
                config.nvme_nsid = 1;  // Default
                config.nvme_lba_size = DEFAULT_LBA_SIZE;  // Default, will be updated from device
                config.nvme_slba = 2000000;  // Default test area
                config.nvme_type = nvme.type;

                // GPU configuration
                config.gpu_device_id = gpu_id;
                cudaDeviceProp prop;
                cudaGetDeviceProperties(&prop, gpu_id);
                config.gpu_name = prop.name;

                configs.push_back(config);
            }
        }

        return configs;
    }
};

/**
 * @brief Base class for performance tests with common functionality
 */
class PerfTestBase : public ::testing::Test {
protected:
    size_t chunk_size = DEFAULT_CHUNK_SIZE;
    int iterations = DEFAULT_ITERATIONS;
    int warmup_iterations = WARMUP_ITERATIONS;

    // Device configuration
    DeviceConfig device_config;

    // Performance statistics
    PerfStats stats;

    void SetUp() override {
        // Initialize from environment or use defaults
        const char* env_val;

        env_val = std::getenv("PERF_ITERATIONS");
        if (env_val) iterations = std::atoi(env_val);

        env_val = std::getenv("PERF_CHUNK_SIZE");
        if (env_val) chunk_size = std::atoi(env_val);

        // Reserve space for statistics
        stats.reserve(iterations);
    }

    void run_warmup(std::function<void()> operation) {
        for (int i = 0; i < warmup_iterations; ++i) {
            operation();
        }
    }

    void execute_gpu_kernel(uint8_t* gpu_data, size_t size, Timer& kernel_timer) {
        kernel_timer.reset();

        int threads_per_block = 256;
        int blocks = (size + threads_per_block - 1) / threads_per_block;

        perf_common::kernels::xor_transform_kernel<<<blocks, threads_per_block>>>(gpu_data, size, 0xAA);
        CUDA_CHECK(cudaDeviceSynchronize());
    }
};

/**
 * @brief Mode names for consistent reporting
 */
namespace ModeNames {
    constexpr const char* MODE_0 = "Mode 0: Baseline (Host + MMIO + Pageable)";
    constexpr const char* MODE_1 = "Mode 1: Pinned (Host + MMIO + Pinned)";
    constexpr const char* MODE_2 = "Mode 2: P2P (Host + MMIO + GPU Buffer)";
    constexpr const char* MODE_3 = "Mode 3: Host DBC (Host + DBC + Host Buffer)";
    constexpr const char* MODE_4 = "Mode 4: GPU DBC (Host + DBC + GPU Buffer)";
    constexpr const char* MODE_5 = "Mode 5: GPU-Init (GPU + DBC + GPU Buffer)";
    constexpr const char* MODE_GDS = "GDS: GPUDirect Storage";
}

} // namespace perf_test
