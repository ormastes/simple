/**
 * @file perf_config.h
 * @brief Performance test configuration
 */

#ifndef PERF_CONFIG_H
#define PERF_CONFIG_H

#include <cstdlib>
#include <string>
#include <cstdint>

namespace perf_common {

/**
 * @brief Performance test configuration singleton
 *
 * Parses environment variables and provides consistent defaults
 */
class PerfConfig {
private:
    // Configuration values
    size_t chunk_size_;
    size_t iterations_;
    size_t warmup_iterations_;
    size_t queue_depth_;

    // NVMe configuration
    std::string nvme_bdf_;
    uint32_t nvme_nsid_;
    uint32_t nvme_lba_size_;
    uint64_t nvme_slba_;

    // GPU configuration
    int cuda_device_id_;
    bool use_cuda_events_;
    bool verbose_output_;

    // Private constructor for singleton
    PerfConfig() {
        parse_environment();
    }

    void parse_environment() {
        // Performance parameters
        chunk_size_ = get_env_size("PERF_CHUNK_SIZE", 4096);
        iterations_ = get_env_size("PERF_ITERATIONS", 1000);
        warmup_iterations_ = get_env_size("PERF_WARMUP", 10);
        queue_depth_ = get_env_size("PERF_QUEUE_DEPTH", 128);

        // NVMe parameters
        nvme_bdf_ = get_env_string("NVME_BDF", "");
        nvme_nsid_ = get_env_uint32("NVME_NSID", 1);
        nvme_lba_size_ = get_env_uint32("NVME_LBA_SIZE", 512);
        nvme_slba_ = get_env_uint64("NVME_SLBA", 2000000);

        // GPU parameters
        cuda_device_id_ = get_env_int("CUDA_DEVICE", 0);
        use_cuda_events_ = get_env_bool("PERF_USE_CUDA_EVENTS", true);
        verbose_output_ = get_env_bool("PERF_VERBOSE", false);
    }

    // Helper methods for environment parsing
    static size_t get_env_size(const char* name, size_t default_value) {
        const char* val = std::getenv(name);
        return val ? std::stoull(val) : default_value;
    }

    static uint32_t get_env_uint32(const char* name, uint32_t default_value) {
        const char* val = std::getenv(name);
        return val ? std::stoul(val) : default_value;
    }

    static uint64_t get_env_uint64(const char* name, uint64_t default_value) {
        const char* val = std::getenv(name);
        return val ? std::stoull(val) : default_value;
    }

    static int get_env_int(const char* name, int default_value) {
        const char* val = std::getenv(name);
        return val ? std::stoi(val) : default_value;
    }

    static bool get_env_bool(const char* name, bool default_value) {
        const char* val = std::getenv(name);
        if (!val) return default_value;
        std::string str(val);
        return str == "1" || str == "true" || str == "TRUE";
    }

    static std::string get_env_string(const char* name, const std::string& default_value) {
        const char* val = std::getenv(name);
        return val ? std::string(val) : default_value;
    }

public:
    /**
     * @brief Get singleton instance
     */
    static PerfConfig& instance() {
        static PerfConfig config;
        return config;
    }

    // Delete copy constructor and assignment
    PerfConfig(const PerfConfig&) = delete;
    PerfConfig& operator=(const PerfConfig&) = delete;

    // Getters
    size_t chunk_size() const { return chunk_size_; }
    size_t iterations() const { return iterations_; }
    size_t warmup_iterations() const { return warmup_iterations_; }
    size_t queue_depth() const { return queue_depth_; }

    const std::string& nvme_bdf() const { return nvme_bdf_; }
    uint32_t nvme_nsid() const { return nvme_nsid_; }
    uint32_t nvme_lba_size() const { return nvme_lba_size_; }
    uint64_t nvme_slba() const { return nvme_slba_; }

    int cuda_device() const { return cuda_device_id_; }
    bool use_cuda_events() const { return use_cuda_events_; }
    bool verbose() const { return verbose_output_; }

    /**
     * @brief Check if NVMe configuration is valid
     */
    bool is_nvme_configured() const {
        return !nvme_bdf_.empty();
    }

    /**
     * @brief Print current configuration
     */
    void print_config() const {
        printf("\n");
        printf("Performance Test Configuration:\n");
        printf("================================\n");
        printf("Chunk Size:       %zu bytes\n", chunk_size_);
        printf("Iterations:       %zu\n", iterations_);
        printf("Warmup:          %zu iterations\n", warmup_iterations_);
        printf("Queue Depth:     %zu\n", queue_depth_);
        printf("\n");
        printf("NVMe Configuration:\n");
        printf("  BDF:           %s\n", nvme_bdf_.c_str());
        printf("  Namespace:     %u\n", nvme_nsid_);
        printf("  LBA Size:      %u bytes\n", nvme_lba_size_);
        printf("  Start LBA:     %lu\n", nvme_slba_);
        printf("\n");
        printf("CUDA Configuration:\n");
        printf("  Device ID:     %d\n", cuda_device_id_);
        printf("  Use Events:    %s\n", use_cuda_events_ ? "Yes" : "No");
        printf("  Verbose:       %s\n", verbose_output_ ? "Yes" : "No");
        printf("================================\n\n");
    }

    /**
     * @brief Override configuration for testing
     */
    void override_chunk_size(size_t size) { chunk_size_ = size; }
    void override_iterations(size_t iters) { iterations_ = iters; }
    void override_warmup(size_t warmup) { warmup_iterations_ = warmup; }
};

/**
 * @brief Test mode definitions with consistent numbering
 */
enum class TestMode {
    MODE_0_BASELINE = 0,            // Host + MMIO + Pageable
    MODE_1_PINNED = 1,              // Host + MMIO + Pinned
    MODE_2_DAEMON_GPU = 2,          // Host + Daemon + GPU Memory
    MODE_3_DBC_HOST = 3,            // Host + DBC + Host Buffer
    MODE_4_DBC_GPU = 4,             // Host + DBC + GPU Buffer
    MODE_5_GPU_INITIATED = 5,       // GPU + DBC + GPU Buffer
    MODE_6_GDS = 6                  // GPUDirect Storage (renamed from Mode 1 GDS)
};

/**
 * @brief Get mode name string
 */
inline const char* get_mode_name(TestMode mode) {
    switch (mode) {
        case TestMode::MODE_0_BASELINE:      return "Mode 0: Baseline";
        case TestMode::MODE_1_PINNED:        return "Mode 1: Pinned Host";
        case TestMode::MODE_2_DAEMON_GPU:    return "Mode 2: Daemon GPU";
        case TestMode::MODE_3_DBC_HOST:      return "Mode 3: DBC Host";
        case TestMode::MODE_4_DBC_GPU:       return "Mode 4: DBC GPU";
        case TestMode::MODE_5_GPU_INITIATED: return "Mode 5: GPU-Initiated";
        case TestMode::MODE_6_GDS:           return "Mode 6: GPUDirect Storage";
        default: return "Unknown Mode";
    }
}

/**
 * @brief Get mode description
 */
inline const char* get_mode_description(TestMode mode) {
    switch (mode) {
        case TestMode::MODE_0_BASELINE:
            return "CPU-managed I/O with pageable host memory (baseline)";
        case TestMode::MODE_1_PINNED:
            return "CPU-managed I/O with pinned host memory";
        case TestMode::MODE_2_DAEMON_GPU:
            return "Host daemon with GPU memory buffer";
        case TestMode::MODE_3_DBC_HOST:
            return "DBC shadow doorbell with host buffer";
        case TestMode::MODE_4_DBC_GPU:
            return "DBC shadow doorbell with GPU buffer";
        case TestMode::MODE_5_GPU_INITIATED:
            return "GPU-initiated I/O with DBC daemon";
        case TestMode::MODE_6_GDS:
            return "NVIDIA GPUDirect Storage (zero-copy path)";
        default:
            return "Unknown mode";
    }
}

} // namespace perf_common

#endif // PERF_CONFIG_H