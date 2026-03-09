/**
 * @file perf_stats.cpp
 * @brief Performance statistics tracking
 */

#include "../include/perf_stats.h"
#include <algorithm>
#include <numeric>
#include <cmath>
#include <iomanip>
#include <iostream>

namespace perf_common {

// Mode descriptors
const ModeDescriptor ModeDescriptor::MODE_0 = {
    0, "mode0", "Mode 0: Baseline",
    "Host + MMIO + Pageable Memory"
};

const ModeDescriptor ModeDescriptor::MODE_1 = {
    1, "mode1", "Mode 1: Pinned",
    "Host + MMIO + Pinned Memory"
};

const ModeDescriptor ModeDescriptor::MODE_2 = {
    2, "mode2", "Mode 2: Daemon GPU",
    "Host + Daemon + GPU Memory"
};

const ModeDescriptor ModeDescriptor::MODE_3 = {
    3, "mode3", "Mode 3: DBC Host",
    "Host + DBC Shadow + Host Buffer"
};

const ModeDescriptor ModeDescriptor::MODE_4 = {
    4, "mode4", "Mode 4: DBC GPU",
    "Host + DBC Shadow + GPU Buffer"
};

const ModeDescriptor ModeDescriptor::MODE_5 = {
    5, "mode5", "Mode 5: GPU-Initiated",
    "GPU + DBC Daemon + GPU Buffer"
};

const ModeDescriptor ModeDescriptor::MODE_6_GDS = {
    6, "mode6_gds", "Mode 6: GPUDirect Storage",
    "NVIDIA GDS Zero-Copy Path"
};

// LatencyStats implementation
void LatencyStats::calculate(const std::vector<uint64_t>& timings_ns) {
    if (timings_ns.empty()) return;

    std::vector<uint64_t> sorted = timings_ns;
    std::sort(sorted.begin(), sorted.end());

    // Convert to microseconds
    min_us = sorted.front() / 1000.0;
    max_us = sorted.back() / 1000.0;

    // Calculate mean
    uint64_t sum = std::accumulate(sorted.begin(), sorted.end(), 0ULL);
    mean_us = (sum / sorted.size()) / 1000.0;

    // Calculate percentiles
    auto get_percentile = [&sorted](double p) {
        size_t idx = static_cast<size_t>((p / 100.0) * sorted.size());
        if (idx >= sorted.size()) idx = sorted.size() - 1;
        return sorted[idx] / 1000.0;
    };

    median_us = get_percentile(50.0);
    p50_us = median_us;
    p95_us = get_percentile(95.0);
    p99_us = get_percentile(99.0);
    p999_us = get_percentile(99.9);

    // Calculate standard deviation
    if (sorted.size() > 1) {
        double sq_sum = 0;
        double mean_ns = mean_us * 1000.0;
        for (uint64_t time : sorted) {
            double diff = time - mean_ns;
            sq_sum += diff * diff;
        }
        stddev_us = std::sqrt(sq_sum / (sorted.size() - 1)) / 1000.0;
    }
}

void LatencyStats::print(const std::string& name) const {
    std::cout << std::fixed << std::setprecision(2);
    std::cout << name << " Latency Statistics (μs):\n";
    std::cout << "  Min:    " << std::setw(8) << min_us << "\n";
    std::cout << "  P50:    " << std::setw(8) << p50_us << "\n";
    std::cout << "  P95:    " << std::setw(8) << p95_us << "\n";
    std::cout << "  P99:    " << std::setw(8) << p99_us << "\n";
    std::cout << "  P99.9:  " << std::setw(8) << p999_us << "\n";
    std::cout << "  Max:    " << std::setw(8) << max_us << "\n";
    std::cout << "  Mean:   " << std::setw(8) << mean_us << "\n";
    std::cout << "  StdDev: " << std::setw(8) << stddev_us << "\n";
}

// IoResult implementation
void IoResult::add_to_stats(PerformanceStats& stats) const {
    stats.add_result(*this);
}

// PerformanceStats implementation
void PerformanceStats::print_summary(const std::string& mode_name, size_t chunk_size) const {
    std::cout << "\n" << std::string(80, '=') << std::endl;
    std::cout << "Performance Results: " << mode_name << std::endl;
    std::cout << std::string(80, '-') << std::endl;

    // Basic metrics
    std::cout << "Operations:      " << total_operations_ << std::endl;
    std::cout << "Chunk Size:      " << chunk_size << " bytes" << std::endl;
    std::cout << "Total Data:      " << std::fixed << std::setprecision(2)
              << (total_bytes_transferred_ / (1024.0 * 1024.0 * 1024.0)) << " GB" << std::endl;

    // Timing breakdown
    if (!total_times_ns_.empty()) {
        std::cout << "\nTiming Breakdown:" << std::endl;

        auto print_component = [this](const std::string& name,
                                      const std::vector<uint64_t>& times) {
            if (times.empty()) return;

            double mean = get_mean(times);
            double p50 = get_percentile(times, 50);
            double p99 = get_percentile(times, 99);

            std::cout << std::fixed << std::setprecision(2);
            std::cout << "  " << std::left << std::setw(15) << name
                     << ": Mean=" << std::setw(8) << mean << " μs"
                     << ", P50=" << std::setw(8) << p50 << " μs"
                     << ", P99=" << std::setw(8) << p99 << " μs" << std::endl;
        };

        print_component("NVMe I/O", nvme_times_ns_);
        print_component("Memory Copy", memcpy_times_ns_);
        print_component("GPU Kernel", kernel_times_ns_);
        print_component("Total", total_times_ns_);
    }

    // Throughput metrics
    std::cout << "\nThroughput Metrics:" << std::endl;
    std::cout << std::fixed << std::setprecision(2);
    std::cout << "  IOPS:        " << std::setw(12) << calculate_iops() << std::endl;
    std::cout << "  Bandwidth:   " << std::setw(12) << calculate_throughput_gbps() << " GB/s" << std::endl;

    // Latency summary
    if (!total_times_ns_.empty()) {
        LatencyStats latency;
        latency.calculate(total_times_ns_);
        std::cout << "\nEnd-to-End ";
        latency.print("Latency");
    }

    std::cout << std::string(80, '=') << std::endl;
}

void PerformanceStats::print_component_breakdown() const {
    if (component_timings_.empty()) {
        std::cout << "No component breakdown available" << std::endl;
        return;
    }

    std::cout << "\nDetailed Component Breakdown:" << std::endl;
    std::cout << std::string(80, '-') << std::endl;

    for (const auto& [component, timings] : component_timings_) {
        if (timings.empty()) continue;

        LatencyStats stats;
        stats.calculate(timings);

        std::cout << "\n" << component << ":" << std::endl;
        std::cout << std::fixed << std::setprecision(2);
        std::cout << "  Mean:  " << std::setw(8) << stats.mean_us << " μs ("
                 << std::setw(5) << (stats.mean_us / get_mean(total_times_ns_) * 100)
                 << "% of total)" << std::endl;
        std::cout << "  P50:   " << std::setw(8) << stats.p50_us << " μs" << std::endl;
        std::cout << "  P99:   " << std::setw(8) << stats.p99_us << " μs" << std::endl;
    }
}

void PerformanceStats::print_comparison_format(const std::string& mode_name) const {
    if (total_times_ns_.empty()) return;

    double mean_latency = get_mean(total_times_ns_);
    double p50_latency = get_percentile(total_times_ns_, 50);
    double p99_latency = get_percentile(total_times_ns_, 99);
    double iops = calculate_iops();
    double bandwidth = calculate_throughput_gbps();

    // Print in table-friendly format
    std::cout << "| " << std::left << std::setw(25) << mode_name
             << " | " << std::right << std::fixed << std::setprecision(2)
             << std::setw(10) << mean_latency << " μs"
             << " | " << std::setw(10) << p50_latency << " μs"
             << " | " << std::setw(10) << p99_latency << " μs"
             << " | " << std::setw(12) << static_cast<int>(iops)
             << " | " << std::setw(8) << bandwidth << " GB/s |" << std::endl;
}

} // namespace perf_common