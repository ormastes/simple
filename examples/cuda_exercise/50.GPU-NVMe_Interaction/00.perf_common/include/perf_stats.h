/**
 * @file perf_stats.h
 * @brief Performance statistics tracking
 */

#ifndef PERF_STATS_H
#define PERF_STATS_H

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>

namespace perf_common {

/**
 * @brief NVMe I/O operation result with detailed timing breakdown
 */
struct IoResult {
    // Total operation time
    uint64_t total_ns = 0;

    // Component timings (all in nanoseconds)
    uint64_t command_build_ns = 0;
    uint64_t submission_ns = 0;
    uint64_t doorbell_ns = 0;
    uint64_t polling_ns = 0;
    uint64_t completion_ns = 0;

    // Memory transfer timings
    uint64_t host_to_gpu_ns = 0;
    uint64_t gpu_to_host_ns = 0;

    // GPU kernel timings
    uint64_t kernel_launch_ns = 0;
    uint64_t kernel_exec_ns = 0;

    // Status
    bool success = false;
    size_t bytes_transferred = 0;

    /**
     * @brief Add this result to cumulative stats
     */
    void add_to_stats(class PerformanceStats& stats) const;
};

/**
 * @brief Latency statistics for a set of measurements
 */
struct LatencyStats {
    double min_us = 0;
    double max_us = 0;
    double mean_us = 0;
    double median_us = 0;
    double p50_us = 0;
    double p95_us = 0;
    double p99_us = 0;
    double p999_us = 0;
    double stddev_us = 0;

    /**
     * @brief Calculate statistics from a vector of timings
     * @param timings_ns Vector of timings in nanoseconds
     */
    void calculate(const std::vector<uint64_t>& timings_ns);

    /**
     * @brief Print formatted statistics
     * @param name Component name for display
     */
    void print(const std::string& name) const;
};

/**
 * @brief Comprehensive performance statistics tracker
 *
 * Tracks component-level timings with flexible granularity
 */
class PerformanceStats {
private:
    // Component timings (nanoseconds)
    std::map<std::string, std::vector<uint64_t>> component_timings_;

    // Aggregated timings for common components
    std::vector<uint64_t> total_times_ns_;
    std::vector<uint64_t> nvme_times_ns_;
    std::vector<uint64_t> memcpy_times_ns_;
    std::vector<uint64_t> kernel_times_ns_;

    // Throughput tracking
    size_t total_bytes_transferred_ = 0;
    size_t total_operations_ = 0;

public:
    /**
     * @brief Reserve space for expected number of iterations
     */
    void reserve(size_t iterations) {
        total_times_ns_.reserve(iterations);
        nvme_times_ns_.reserve(iterations);
        memcpy_times_ns_.reserve(iterations);
        kernel_times_ns_.reserve(iterations);
    }

    /**
     * @brief Add a single I/O result
     */
    void add_result(const IoResult& result) {
        total_times_ns_.push_back(result.total_ns);
        nvme_times_ns_.push_back(result.submission_ns + result.doorbell_ns +
                                 result.polling_ns + result.completion_ns);
        memcpy_times_ns_.push_back(result.host_to_gpu_ns + result.gpu_to_host_ns);
        kernel_times_ns_.push_back(result.kernel_exec_ns);

        total_bytes_transferred_ += result.bytes_transferred;
        total_operations_++;

        // Track detailed components
        add_component_timing("command_build", result.command_build_ns);
        add_component_timing("submission", result.submission_ns);
        add_component_timing("doorbell", result.doorbell_ns);
        add_component_timing("polling", result.polling_ns);
        add_component_timing("completion", result.completion_ns);
        add_component_timing("h2d_copy", result.host_to_gpu_ns);
        add_component_timing("d2h_copy", result.gpu_to_host_ns);
        add_component_timing("kernel", result.kernel_exec_ns);
    }

    /**
     * @brief Add timing for a specific component
     */
    void add_component_timing(const std::string& component, uint64_t time_ns) {
        component_timings_[component].push_back(time_ns);
    }

    /**
     * @brief Add simple iteration timing (backward compatibility)
     */
    void add_iteration(double nvme_ms, double memcpy_ms, double kernel_ms) {
        nvme_times_ns_.push_back(static_cast<uint64_t>(nvme_ms * 1000000));
        memcpy_times_ns_.push_back(static_cast<uint64_t>(memcpy_ms * 1000000));
        kernel_times_ns_.push_back(static_cast<uint64_t>(kernel_ms * 1000000));
        total_times_ns_.push_back(static_cast<uint64_t>(
            (nvme_ms + memcpy_ms + kernel_ms) * 1000000));
        total_operations_++;
    }

    /**
     * @brief Get percentile from a timing vector
     */
    static double get_percentile(const std::vector<uint64_t>& times_ns, double percentile) {
        if (times_ns.empty()) return 0.0;

        std::vector<uint64_t> sorted = times_ns;
        std::sort(sorted.begin(), sorted.end());

        size_t idx = static_cast<size_t>((percentile / 100.0) * sorted.size());
        if (idx >= sorted.size()) idx = sorted.size() - 1;

        return sorted[idx] / 1000.0;  // Return in microseconds
    }

    /**
     * @brief Get mean of a timing vector
     */
    static double get_mean(const std::vector<uint64_t>& times_ns) {
        if (times_ns.empty()) return 0.0;

        uint64_t sum = std::accumulate(times_ns.begin(), times_ns.end(), 0ULL);
        return (sum / times_ns.size()) / 1000.0;  // Return in microseconds
    }

    /**
     * @brief Get standard deviation of a timing vector
     */
    static double get_stddev(const std::vector<uint64_t>& times_ns) {
        if (times_ns.size() < 2) return 0.0;

        double mean = get_mean(times_ns) * 1000.0;  // Convert back to ns
        double sq_sum = 0;

        for (uint64_t time : times_ns) {
            double diff = time - mean;
            sq_sum += diff * diff;
        }

        return std::sqrt(sq_sum / (times_ns.size() - 1)) / 1000.0;  // Return in us
    }

    /**
     * @brief Calculate IOPS (I/O operations per second)
     */
    double calculate_iops() const {
        if (total_times_ns_.empty()) return 0.0;

        uint64_t total_time_ns = std::accumulate(total_times_ns_.begin(),
                                                 total_times_ns_.end(), 0ULL);
        double total_time_s = total_time_ns / 1000000000.0;

        return total_operations_ / total_time_s;
    }

    /**
     * @brief Calculate throughput in GB/s
     */
    double calculate_throughput_gbps() const {
        if (total_times_ns_.empty()) return 0.0;

        uint64_t total_time_ns = std::accumulate(total_times_ns_.begin(),
                                                 total_times_ns_.end(), 0ULL);
        double total_time_s = total_time_ns / 1000000000.0;
        double total_gb = total_bytes_transferred_ / (1024.0 * 1024.0 * 1024.0);

        return total_gb / total_time_s;
    }

    /**
     * @brief Print comprehensive performance summary
     */
    void print_summary(const std::string& mode_name, size_t chunk_size = 4096) const;

    /**
     * @brief Print detailed component breakdown
     */
    void print_component_breakdown() const;

    /**
     * @brief Print comparison table format
     */
    void print_comparison_format(const std::string& mode_name) const;

    // Getters for specific timing vectors
    const std::vector<uint64_t>& get_total_times() const { return total_times_ns_; }
    const std::vector<uint64_t>& get_nvme_times() const { return nvme_times_ns_; }
    const std::vector<uint64_t>& get_memcpy_times() const { return memcpy_times_ns_; }
    const std::vector<uint64_t>& get_kernel_times() const { return kernel_times_ns_; }
    size_t get_operation_count() const { return total_operations_; }
    size_t get_bytes_transferred() const { return total_bytes_transferred_; }
};

/**
 * @brief Mode descriptor for consistent naming
 */
struct ModeDescriptor {
    int mode_number;
    std::string short_name;
    std::string full_name;
    std::string description;

    static const ModeDescriptor MODE_0;
    static const ModeDescriptor MODE_1;
    static const ModeDescriptor MODE_2;
    static const ModeDescriptor MODE_3;
    static const ModeDescriptor MODE_4;
    static const ModeDescriptor MODE_5;
    static const ModeDescriptor MODE_6_GDS;  // Renamed from Mode 1 GDS
};

} // namespace perf_common

#endif // PERF_STATS_H
