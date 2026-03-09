/**
 * @file benchmark_base.h
 * @brief Common definitions and utilities for benchmarks
 */

#ifndef BENCHMARK_BASE_H
#define BENCHMARK_BASE_H

#include <cstdint>
#include <vector>
#include <string>

// Result structure for individual read operations
struct ReadResult {
    uint64_t total_ns;              // Total latency
    uint64_t kernel_launch_ns;      // Kernel launch overhead (GPU only)
    uint64_t command_build_ns;      // Command building time
    uint64_t submission_ns;         // Queue submission time
    uint64_t doorbell_ns;           // Doorbell ring time
    uint64_t completion_ns;         // Completion polling time
    uint64_t copy_to_gpu_ns;        // Host-to-GPU copy (if applicable)
    bool success;                   // Operation success flag

    ReadResult() : total_ns(0), kernel_launch_ns(0), command_build_ns(0),
                   submission_ns(0), doorbell_ns(0), completion_ns(0),
                   copy_to_gpu_ns(0), success(false) {}
};

// Submission timing details
struct SubmissionTimings {
    uint64_t command_build_ns;
    uint64_t tail_update_ns;
    uint64_t doorbell_ns;
};

// Component breakdown for analysis
struct ComponentBreakdown {
    double kernel_launch_us;
    double cmd_build_us;
    double submission_us;
    double doorbell_us;
    double device_us;
    double completion_us;
};

// Benchmark configuration
struct BenchmarkConfig {
    uint64_t num_iterations;
    bool sequential_lbas;
    bool measure_gpu_copy;
    uint64_t start_lba;
    std::string output_file;

    BenchmarkConfig()
        : num_iterations(10000),
          sequential_lbas(true),
          measure_gpu_copy(false),
          start_lba(0),
          output_file("") {}
};

// Statistical analysis results
struct LatencyStats {
    double min_us;
    double max_us;
    double mean_us;
    double median_us;
    double p95_us;
    double p99_us;
    double stddev_us;
};

// Calculate statistics from results
LatencyStats calculate_statistics(const std::vector<ReadResult>& results);

// Print statistics table
void print_statistics(const LatencyStats& stats, const std::string& label);

// Print component breakdown
void print_component_breakdown(const std::vector<ReadResult>& results,
                               bool is_gpu_submission);

#endif // BENCHMARK_BASE_H
