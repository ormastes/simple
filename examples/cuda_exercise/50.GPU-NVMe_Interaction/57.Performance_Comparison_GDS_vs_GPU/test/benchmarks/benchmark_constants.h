/**
 * @file benchmark_constants.h
 * @brief Common constants for Mode 0-6 benchmarks
 *
 * Eliminates magic numbers and provides consistent configuration
 * across all benchmark implementations.
 *
 * IMPORTANT: Use get_page_size() and get_lba_size() helpers instead of
 * hardcoded constants when NvmeDevice is available. The constants here
 * are fallback defaults only.
 */

#pragma once

#include <cstdint>
#include <cstdlib>
#include <cctype>
#include <string>

// Forward declaration for device-aware helpers
struct NvmeDevice;
extern "C" {
    size_t nvme_get_page_size(NvmeDevice* d);
    uint32_t nvme_get_lba_size(NvmeDevice* d);
}

namespace benchmark_constants {

// ============================================================================
// NVMe Configuration (Default Values - prefer device queries when available)
// ============================================================================

/// Default LBA size in bytes (512B standard sector size)
/// @note Use get_lba_size_from_device() when NvmeDevice is available
constexpr uint32_t DEFAULT_LBA_SIZE = 512;

/// Default page size for alignment
/// @note Use get_page_size_from_device() when NvmeDevice is available
constexpr size_t DEFAULT_PAGE_SIZE = 4096;

/// Default buffer size for 4KB I/O (8 LBAs × 512B)
constexpr size_t DEFAULT_BUFFER_SIZE_4KB = 4096;

/// Default number of LBAs per 4KB I/O (0-based: 7 = 8 LBAs)
constexpr uint16_t DEFAULT_NLBS_4KB = 7;

// Legacy aliases for backward compatibility
/// @deprecated Use DEFAULT_LBA_SIZE instead
constexpr uint32_t LBA_SIZE = DEFAULT_LBA_SIZE;

/// @deprecated Use DEFAULT_BUFFER_SIZE_4KB instead
constexpr size_t BUFFER_SIZE_4KB = DEFAULT_BUFFER_SIZE_4KB;

/// @deprecated Use DEFAULT_NLBS_4KB instead
constexpr uint16_t NLBS_4KB = DEFAULT_NLBS_4KB;

/// @deprecated Use DEFAULT_PAGE_SIZE instead
constexpr size_t PAGE_SIZE = DEFAULT_PAGE_SIZE;

// ============================================================================
// Queue Configuration
// ============================================================================

/// Default submission queue depth
constexpr uint16_t DEFAULT_SQ_DEPTH = 64;

/// Default completion queue depth
constexpr uint16_t DEFAULT_CQ_DEPTH = 1024;

/// Default namespace ID
constexpr uint32_t DEFAULT_NSID = 1;

/// Default queue ID for I/O queue
constexpr uint16_t DEFAULT_QID = 1;

// ============================================================================
// Benchmark Configuration
// ============================================================================

/// Default number of benchmark iterations
/// Note: For GPU-initiated modes (4-6), limited to queue depth - 1 to avoid wrap issues
constexpr uint64_t DEFAULT_ITERATIONS = 1000;

/// Maximum iterations for GPU-initiated modes (queue wrap limitation)
/// TODO: Fix queue wrap handling in Mode5Daemon for unlimited iterations
constexpr uint64_t MAX_GPU_INITIATED_ITERATIONS = 1000;

/// Warmup iterations before measurement
constexpr uint32_t WARMUP_ITERATIONS = 100;

/// Default starting LBA for tests
constexpr uint64_t DEFAULT_START_LBA = 2000000;

/// Progress update interval (every N iterations)
constexpr uint64_t PROGRESS_INTERVAL = 1000;

// ============================================================================
// Timeout Configuration
// ============================================================================

/// Completion polling timeout in microseconds
constexpr uint32_t POLL_TIMEOUT_US = 10000000;  // 10 seconds

/// Daemon polling interval in microseconds
constexpr uint32_t DAEMON_POLL_INTERVAL_US = 1;

// ============================================================================
// P2P Configuration
// ============================================================================

/// Maximum P2P segments
constexpr uint32_t MAX_P2P_SEGMENTS = 16;

// ============================================================================
// Environment Variable Helpers
// ============================================================================

/**
 * @brief Get NVMe BDF from environment variable (required)
 * @return BDF string or nullptr if not set
 */
inline const char* get_nvme_bdf_required() {
    const char* bdf = std::getenv("NVME_BDF");
    if (!bdf) {
        fprintf(stderr, "ERROR: NVME_BDF environment variable not set\n");
        fprintf(stderr, "Usage: export NVME_BDF='0000:XX:00.0'\n");
        exit(1);
    }
    return bdf;
}

/**
 * @brief Require P2P path (set REQUIRE_P2P=1 or NVME_REQUIRE_P2P=1)
 */
inline bool require_p2p_enabled() {
    const char* env = std::getenv("REQUIRE_P2P");
    if (!env) env = std::getenv("NVME_REQUIRE_P2P");
    if (!env) return true;  // Default: require P2P unless explicitly disabled
    char c = static_cast<char>(std::tolower(env[0]));
    return c == '1' || c == 'y' || c == 't';
}

/**
 * @brief Get number of iterations from environment or default
 * @param default_val Default value if env var not set
 * @return Number of iterations
 */
inline uint64_t get_iterations(uint64_t default_val = DEFAULT_ITERATIONS) {
    const char* env = std::getenv("BENCHMARK_ITERATIONS");
    if (!env) {
        env = std::getenv("BENCH_ITERATIONS");
    }
    const uint64_t iterations = env ? std::stoull(env) : default_val;
    return iterations == 0 ? default_val : iterations;
}

/**
 * @brief Get starting LBA from environment or default
 * @param default_val Default value if env var not set
 * @return Starting LBA
 */
inline uint64_t get_start_lba(uint64_t default_val = DEFAULT_START_LBA) {
    const char* env = std::getenv("NVME_SLBA");
    return env ? std::stoull(env) : default_val;
}

/**
 * @brief Get LBA size from environment or default
 * @param default_val Default value if env var not set
 * @return LBA size in bytes
 */
inline uint32_t get_lba_size(uint32_t default_val = DEFAULT_LBA_SIZE) {
    const char* env = std::getenv("NVME_LBA_SIZE");
    return env ? std::stoul(env) : default_val;
}

/**
 * @brief Get namespace ID from environment or default
 * @param default_val Default value if env var not set
 * @return Namespace ID
 */
inline uint32_t get_nsid(uint32_t default_val = DEFAULT_NSID) {
    const char* env = std::getenv("NVME_NSID");
    return env ? std::stoul(env) : default_val;
}

// ============================================================================
// Device-Aware Helpers (Preferred over hardcoded constants)
// ============================================================================

/**
 * @brief Get LBA size from NvmeDevice (preferred) or environment/default
 * @param device NvmeDevice pointer (can be nullptr for fallback)
 * @return LBA size in bytes from device, env var, or default
 */
inline uint32_t get_lba_size_from_device(NvmeDevice* device) {
    if (device) {
        return nvme_get_lba_size(device);
    }
    return get_lba_size();
}

/**
 * @brief Get page size from NvmeDevice (preferred) or environment/default
 * @param device NvmeDevice pointer (can be nullptr for fallback)
 * @return Page size in bytes from device or default
 */
inline size_t get_page_size_from_device(NvmeDevice* device) {
    if (device) {
        return nvme_get_page_size(device);
    }
    // No env var for page size, use default
    return DEFAULT_PAGE_SIZE;
}

/**
 * @brief Calculate NLB (Number of Logical Blocks - 1) for a given I/O size
 * @param io_size_bytes Size of I/O in bytes
 * @param lba_size LBA size in bytes
 * @return NLB value (0-based count for NVMe command CDW12)
 */
inline uint16_t calculate_nlb(size_t io_size_bytes, uint32_t lba_size) {
    if (lba_size == 0) return 0;
    uint32_t num_blocks = static_cast<uint32_t>(io_size_bytes / lba_size);
    return (num_blocks > 0) ? static_cast<uint16_t>(num_blocks - 1) : 0;
}

/**
 * @brief Calculate NLB using device LBA size
 * @param io_size_bytes Size of I/O in bytes
 * @param device NvmeDevice pointer (can be nullptr for fallback)
 * @return NLB value (0-based count for NVMe command CDW12)
 */
inline uint16_t calculate_nlb_from_device(size_t io_size_bytes, NvmeDevice* device) {
    return calculate_nlb(io_size_bytes, get_lba_size_from_device(device));
}

} // namespace benchmark_constants
