/**
 * @file host_benchmark.cpp
 * @brief Host-side implementation for host_benchmark
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// host_benchmark.cpp - Benchmarking for host-based submission
#include <vector>
#include <numeric>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <getopt.h>
#include "common/benchmark_base.h"
#include "host/host_submission.cpp"

/**
 * Host submission benchmark class
 */
class HostBenchmark {
public:
    void run_latency_benchmark(const BenchmarkConfig& config) {
        printf("=== Host Submission Latency Benchmark ===\n");
        printf("Iterations: %lu\n", config.num_iterations);
        printf("Sequential LBAs: %s\n", config.sequential_lbas ? "yes" : "no");
        printf("Start LBA: %lu\n\n", config.start_lba);

        HostSubmission submitter(config.measure_gpu_copy);
        std::vector<ReadResult> results;
        results.reserve(config.num_iterations);

        // Warm-up phase
        printf("Warming up (100 iterations)...\n");
        for (int i = 0; i < 100; ++i) {
            submitter.read_4kb_sync(config.start_lba);
        }

        // Actual benchmark
        printf("Running benchmark...\n");
        for (uint64_t i = 0; i < config.num_iterations; ++i) {
            uint64_t lba = config.sequential_lbas ?
                (config.start_lba + i) :
                (config.start_lba + (rand() % 10000));

            results.push_back(submitter.read_4kb_sync(lba));

            // Progress indicator
            if ((i + 1) % 1000 == 0) {
                printf("  Progress: %lu / %lu\n", i + 1, config.num_iterations);
            }
        }

        printf("\n");
        analyze_latency(results);
    }

    void run_throughput_benchmark(const BenchmarkConfig& config) {
        printf("=== Host Submission Throughput Benchmark ===\n");

        HostSubmission submitter(false);

        // Generate LBA list
        std::vector<uint64_t> lbas;
        for (uint64_t i = 0; i < config.num_iterations; ++i) {
            lbas.push_back(config.start_lba + i);
        }

        auto start = std::chrono::high_resolution_clock::now();

        std::vector<ReadResult> results(lbas.size());
        submitter.read_4kb_batch(lbas, results);

        auto end = std::chrono::high_resolution_clock::now();

        double elapsed_sec = std::chrono::duration<double>(end - start).count();
        double iops = config.num_iterations / elapsed_sec;
        double bandwidth_mbs = (iops * 4096) / (1024 * 1024);

        printf("Throughput: %.2f IOPS, %.2f MB/s\n", iops, bandwidth_mbs);
    }

private:
    void analyze_latency(const std::vector<ReadResult>& results) {
        // Extract total latencies
        std::vector<uint64_t> latencies;
        for (const auto& r : results) {
            latencies.push_back(r.total_ns);
        }

        std::sort(latencies.begin(), latencies.end());

        uint64_t min = latencies.front();
        uint64_t max = latencies.back();
        uint64_t median = latencies[latencies.size() / 2];
        uint64_t p95 = latencies[latencies.size() * 95 / 100];
        uint64_t p99 = latencies[latencies.size() * 99 / 100];

        uint64_t sum = std::accumulate(latencies.begin(), latencies.end(), 0ULL);
        double mean = static_cast<double>(sum) / latencies.size();

        printf("Latency Statistics (μs):\n");
        printf("  Min:    %.2f\n", min / 1000.0);
        printf("  Mean:   %.2f\n", mean / 1000.0);
        printf("  Median: %.2f\n", median / 1000.0);
        printf("  P95:    %.2f\n", p95 / 1000.0);
        printf("  P99:    %.2f\n", p99 / 1000.0);
        printf("  Max:    %.2f\n\n", max / 1000.0);

        // Component breakdown
        uint64_t avg_cmd = 0, avg_sub = 0, avg_db = 0, avg_cpl = 0;
        for (const auto& r : results) {
            avg_cmd += r.command_build_ns;
            avg_sub += r.submission_ns;
            avg_db += r.doorbell_ns;
            avg_cpl += r.completion_ns;
        }

        printf("Component Breakdown (average μs):\n");
        printf("  Command Build: %.2f\n", (avg_cmd / results.size()) / 1000.0);
        printf("  Submission:    %.2f\n", (avg_sub / results.size()) / 1000.0);
        printf("  Doorbell:      %.2f\n", (avg_db / results.size()) / 1000.0);
        printf("  Completion:    %.2f\n", (avg_cpl / results.size()) / 1000.0);
    }
};

int main(int argc, char** argv) {
    BenchmarkConfig config;
    config.num_iterations = 10000;
    config.sequential_lbas = true;
    config.start_lba = 0;

    // Parse command line arguments
    static struct option long_opts[] = {
        {"iterations", required_argument, nullptr, 'n'},
        {"start-lba", required_argument, nullptr, 's'},
        {"random", no_argument, nullptr, 'r'},
        {"measure-gpu-copy", no_argument, nullptr, 'g'},
        {nullptr, 0, nullptr, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "n:s:rg", long_opts, nullptr)) != -1) {
        switch (opt) {
        case 'n':
            config.num_iterations = std::strtoull(optarg, nullptr, 10);
            break;
        case 's':
            config.start_lba = std::strtoull(optarg, nullptr, 10);
            break;
        case 'r':
            config.sequential_lbas = false;
            break;
        case 'g':
            config.measure_gpu_copy = true;
            break;
        default:
            fprintf(stderr, "Usage: %s [--iterations N] [--start-lba LBA] [--random] [--measure-gpu-copy]\n", argv[0]);
            return 1;
        }
    }

    HostBenchmark benchmark;
    benchmark.run_latency_benchmark(config);

    return 0;
}
