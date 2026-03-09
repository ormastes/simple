/**
 * @file log_helper.h
 * @brief Logging utilities for system tests
 *
 * Provides consistent formatted output for common test logging patterns:
 * - Device properties
 * - I/O operation details
 * - Performance metrics
 * - Error information
 * - Test skip helper macros
 */

#pragma once

#include <algorithm>
#include <cstdio>
#include <cstdint>
#include <string>
#include <vector>
#include <cstdlib>
#include <cstring>

#define RETURN_IF_QUIET() \
    do { \
        if (test_log::is_quiet()) return; \
    } while (0)

/**
 * @brief Check condition and skip test if false
 *
 * Executes the condition expression and skips the test with the provided
 * log message if the condition evaluates to false.
 *
 * @param condition Expression that returns bool (e.g., function call)
 * @param log_msg String or expression that provides skip reason
 *
 * Usage:
 * @code
 * CHECK_SKIP(select_test_devices(...), skip_reason_);
 * CHECK_SKIP(setup_helper_->setup_all(), "SetupHelper failed");
 * @endcode
 */
#define CHECK_SKIP(condition, log_msg) \
    do { \
        if (!(condition)) { \
            GTEST_SKIP() << (log_msg); \
        } \
    } while (0)

/**
 * @brief Check condition, execute cleanup, and skip test if false
 *
 * Executes the condition expression, runs cleanup code if false,
 * then skips the test with the provided log message.
 *
 * @param condition Expression that returns bool (e.g., function call)
 * @param cleanup Statement(s) to execute before skip (e.g., resource cleanup)
 * @param log_msg String or expression that provides skip reason
 *
 * Usage:
 * @code
 * CHECK_SKIP_CLEANUP(
 *     setup_helper_->setup_all(),
 *     setup_helper_.reset(),
 *     "SetupHelper failed"
 * );
 *
 * CHECK_SKIP_CLEANUP(
 *     dev != nullptr,
 *     { cleanup_resources(); log_failure(); },
 *     "Device is null"
 * );
 * @endcode
 */
#define CHECK_SKIP_CLEANUP(condition, cleanup, log_msg) \
    do { \
        if (!(condition)) { \
            cleanup; \
            GTEST_SKIP() << (log_msg); \
        } \
    } while (0)

namespace test_log {

/**
 * @brief Check if test logging should be suppressed
 *
 * Controlled by TEST_LOG_QUIET env var (any non-empty value enables quiet mode).
 */
inline bool is_quiet() {
    const char* env = std::getenv("TEST_LOG_QUIET");
    return env && env[0] != '\0' && std::strcmp(env, "0") != 0;
}

/**
 * @brief Log device properties
 */
inline void log_device_properties(uint32_t page_size, uint32_t max_page_size,
                                   uint32_t lba_size, uint32_t item_size, uint32_t num_lbas) {
    RETURN_IF_QUIET();
    printf("Device Properties:\n");
    printf("  Page Size:     %u bytes\n", page_size);
    printf("  Max Page Size: %u bytes\n", max_page_size);
    printf("  LBA Size:      %u bytes\n", lba_size);
    printf("  Item Size:     %u bytes (%u LBAs)\n", item_size, num_lbas);
}

/**
 * @brief Log pool properties
 */
inline void log_pool_properties(uint32_t capacity, size_t buf_size, uint32_t in_use) {
    RETURN_IF_QUIET();
    printf("Pool Properties:\n");
    printf("  Capacity:  %u buffers\n", capacity);
    printf("  Buf Size:  %zu bytes\n", buf_size);
    printf("  In Use:    %u buffers\n", in_use);
}

/**
 * @brief Log CUDA device properties
 */
inline void log_cuda_device_properties(int device_id, const char* name, int major, int minor,
                                        size_t total_memory, bool can_map_host) {
    RETURN_IF_QUIET();
    printf("CUDA Device %d: %s\n", device_id, name);
    printf("  Compute Capability: %d.%d\n", major, minor);
    printf("  Total Global Memory: %.2f GB\n", total_memory / (1024.0 * 1024.0 * 1024.0));
    printf("  Can Map Host Memory: %s\n", can_map_host ? "Yes" : "No");
}

/**
 * @brief Log I/O submission details
 */
inline void log_io_submission(const char* op_type, uint32_t nsid, uint64_t slba,
                               size_t bytes, void* addr, uint64_t iova) {
    RETURN_IF_QUIET();
    printf("Submitting %s command:\n", op_type);
    printf("  NSID: %u, SLBA: %lu, Size: %zu bytes\n", nsid, slba, bytes);
    printf("  Buffer: addr=%p, bytes=%zu, iova=%lx\n", addr, bytes, iova);
}

/**
 * @brief Log queue details
 */
inline void log_queue_details(void* vaddr, void* db, void* read_pool, void* write_pool) {
    RETURN_IF_QUIET();
    printf("  Queue: vaddr=%p, db=%p, read_pool=%p, write_pool=%p\n",
           vaddr, db, read_pool, write_pool);
}

/**
 * @brief Log NVMe error status
 */
inline void log_nvme_error(uint8_t sct, uint8_t sc, uint8_t dnr) {
    RETURN_IF_QUIET();
    printf("Error detected:\n");
    printf("  SCT: %u (Status Code Type)\n", sct);
    printf("  SC:  %u (Status Code)\n", sc);
    printf("  DNR: %u (Do Not Retry)\n", dnr);
}

/**
 * @brief Log benchmark configuration
 */
inline void log_benchmark_config(uint16_t num_ops, size_t io_size) {
    RETURN_IF_QUIET();
    printf("Starting benchmark...\n");
    printf("  Operations: %u\n", num_ops);
    printf("  I/O Size:   %zu bytes\n", io_size);
    printf("  Total Data: %.2f MB\n", (num_ops * io_size) / (1024.0 * 1024.0));
}

/**
 * @brief Log performance metrics
 */
inline void log_performance_metrics(double elapsed_sec, double throughput_mbps,
                                    double iops, double avg_latency_us, double total_mb) {
    RETURN_IF_QUIET();
    printf("Performance Metrics:\n");
    printf("  Total Time:       %.3f seconds\n", elapsed_sec);
    printf("  Throughput:       %.2f MB/s\n", throughput_mbps);
    printf("  IOPS:             %.2f ops/s\n", iops);
    printf("  Avg Latency:      %.2f μs\n", avg_latency_us);
    printf("  Data Transferred: %.2f MB\n", total_mb);
}

/**
 * @brief Log latency percentiles
 */
inline void log_latency_percentiles(double min, double avg, double p50,
                                     double p90, double p99, double p999, double max) {
    RETURN_IF_QUIET();
    printf("Latency Distribution (μs):\n");
    printf("  Min:      %.2f\n", min);
    printf("  Average:  %.2f\n", avg);
    printf("  P50:      %.2f\n", p50);
    printf("  P90:      %.2f\n", p90);
    printf("  P99:      %.2f\n", p99);
    printf("  P99.9:    %.2f\n", p999);
    printf("  Max:      %.2f\n", max);
}

/**
 * @brief Log queue depth performance result
 */
inline void log_qd_result(uint16_t queue_depth, double iops, double throughput_mbps,
                          double avg_latency_us) {
    RETURN_IF_QUIET();
    printf("  QD=%2u: %7.2f IOPS, %7.2f MB/s, %.2f μs avg latency\n",
           queue_depth, iops, throughput_mbps, avg_latency_us);
}

/**
 * @brief Log environment variable status
 */
inline void log_env_var(const char* name, const char* value, const char* default_val = nullptr) {
    RETURN_IF_QUIET();
    if (value && value[0] != '\0') {
        printf("  %s: %s\n", name, value);
    } else if (default_val) {
        printf("  %s: (default: %s)\n", name, default_val);
    } else {
        printf("  %s: (not set)\n", name);
    }
}

/**
 * @brief Calculate and log performance metrics from benchmark timing
 * @param duration_us Duration in microseconds
 * @param num_ops Number of operations performed
 * @param io_size Size of each I/O operation in bytes
 */
inline void calculate_and_log_performance(uint64_t duration_us, uint16_t num_ops, size_t io_size) {
    RETURN_IF_QUIET();
    double elapsed_sec = duration_us / 1e6;
    double total_mb = (num_ops * io_size) / (1024.0 * 1024.0);
    double throughput_mbps = total_mb / elapsed_sec;
    double iops = num_ops / elapsed_sec;
    double avg_latency_us = duration_us / (double)num_ops;

    log_performance_metrics(elapsed_sec, throughput_mbps, iops, avg_latency_us, total_mb);
}

/**
 * @brief Calculate and log latency statistics from samples
 * @param latencies Vector of latency samples (will be sorted in-place)
 */
inline void calculate_and_log_latency_stats(std::vector<double>& latencies) {
    RETURN_IF_QUIET();
    std::sort(latencies.begin(), latencies.end());

    double min = latencies.front();
    double max = latencies.back();
    double sum = 0;
    for (double lat : latencies) sum += lat;
    double avg = sum / latencies.size();

    double p50 = latencies[latencies.size() * 50 / 100];
    double p90 = latencies[latencies.size() * 90 / 100];
    double p99 = latencies[latencies.size() * 99 / 100];
    double p999 = latencies[latencies.size() * 999 / 1000];

    log_latency_percentiles(min, avg, p50, p90, p99, p999, max);
}

/**
 * @brief Calculate and log queue depth performance result
 * @param duration_us Duration in microseconds
 * @param queue_depth Queue depth used
 * @param total_ops Total operations performed
 * @param io_size Size of each I/O operation in bytes
 */
inline void calculate_and_log_qd_result(uint64_t duration_us, uint16_t queue_depth,
                                        uint16_t total_ops, size_t io_size) {
    RETURN_IF_QUIET();
    double elapsed_sec = duration_us / 1e6;
    double iops = total_ops / elapsed_sec;
    double throughput_mbps = (total_ops * io_size) / (1024.0 * 1024.0 * elapsed_sec);
    double avg_latency_us = duration_us / (double)total_ops;

    log_qd_result(queue_depth, iops, throughput_mbps, avg_latency_us);
}

/**
 * @brief Calculate and log performance comparison between two approaches
 * @param duration_baseline_us Baseline duration in microseconds
 * @param duration_optimized_us Optimized duration in microseconds
 * @param num_ops Number of operations performed
 * @param io_size Size of each I/O operation in bytes
 * @param baseline_label Label for baseline approach (e.g., "Regular Buffer")
 * @param optimized_label Label for optimized approach (e.g., "CUDA-Pinned Buffer")
 */
inline void calculate_and_log_performance_comparison(
    uint64_t duration_baseline_us, uint64_t duration_optimized_us,
    uint16_t num_ops, size_t io_size,
    const char* baseline_label, const char* optimized_label) {
    RETURN_IF_QUIET();

    // Baseline calculations
    double time_baseline_sec = duration_baseline_us / 1e6;
    double total_mb_baseline = (num_ops * io_size) / (1024.0 * 1024.0);
    double throughput_baseline = total_mb_baseline / time_baseline_sec;
    double iops_baseline = num_ops / time_baseline_sec;
    double avg_latency_baseline = duration_baseline_us / (double)num_ops;

    // Optimized calculations
    double time_optimized_sec = duration_optimized_us / 1e6;
    double total_mb_optimized = (num_ops * io_size) / (1024.0 * 1024.0);
    double throughput_optimized = total_mb_optimized / time_optimized_sec;
    double iops_optimized = num_ops / time_optimized_sec;
    double avg_latency_optimized = duration_optimized_us / (double)num_ops;

    // Speedup
    double speedup = iops_optimized / iops_baseline;

    printf("\n=== Performance Results ===\n");
    printf("%s:\n", baseline_label);
    log_performance_metrics(time_baseline_sec, throughput_baseline, iops_baseline,
                           avg_latency_baseline, total_mb_baseline);
    printf("\n%s:\n", optimized_label);
    log_performance_metrics(time_optimized_sec, throughput_optimized, iops_optimized,
                           avg_latency_optimized, total_mb_optimized);
    printf("\nSpeedup: %.2fx\n", speedup);
    printf("===========================\n");
}

}  // namespace test_log
