/**
 * @file gds_benchmark.cpp
 * @brief Host-side implementation for gds_benchmark
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// gds_benchmark.cpp - GPUDirect Storage benchmark (host command submission)
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <numeric>
#include <cstring>
#include "common/benchmark_base.h"
#include "common/timer.h"
#include "mapper/mapper_host.h"
#include "nvme_vio_cuda_host.h"
#include "kernels/sum_kernel.h"

/**
 * GPUDirect Storage Benchmark
 *
 * This class implements host-based NVMe command submission with GPU pinned memory.
 * Data is read directly into GPU-accessible memory, then processed by GPU kernels.
 */
class GDSBenchmark {
private:
    NvmeDevice* nvme_device_;
    Buffer* gpu_buffer_;           // GPU pinned memory buffer
    uint32_t* d_sum_result_;       // Device pointer for sum result
    cudaStream_t stream_;
    Queue* iosq_;
    Queue* iocq_;
    uint16_t cmd_id_;

    static constexpr size_t BLOCK_SIZE = 4096;  // 4KB
    static constexpr size_t NUM_BLOCKS = 1;     // Reading 1 block (4KB)

public:
    GDSBenchmark(const char* nvme_bdf) : cmd_id_(0) {
        // Open NVMe device
        nvme_device_ = nvme_open(nvme_bdf, 64, 1024, 512);
        if (!nvme_device_) {
            fprintf(stderr, "Failed to open NVMe device %s\n", nvme_bdf);
            exit(1);
        }

        iosq_ = nvme_get_iosq(nvme_device_);
        iocq_ = nvme_get_iocq(nvme_device_);

        // Create GPU pinned consecutive buffer (4KB)
        gpu_buffer_ = nvme_host_create_cuda_pinned_consecutive_buffer(BLOCK_SIZE);
        if (!gpu_buffer_ || !gpu_buffer_->addr) {
            fprintf(stderr, "Failed to create CUDA pinned buffer\n");
            exit(1);
        }

        printf("GDS Buffer created: addr=%p, iova=0x%lx, size=%zu\n",
               gpu_buffer_->addr, gpu_buffer_->iova, gpu_buffer_->bytes);

        // Allocate device memory for sum result
        cudaMalloc(&d_sum_result_, sizeof(uint32_t));

        // Create CUDA stream
        cudaStreamCreate(&stream_);
    }

    ~GDSBenchmark() {
        if (stream_) cudaStreamDestroy(stream_);
        if (d_sum_result_) cudaFree(d_sum_result_);
        if (gpu_buffer_) nvme_cuda_host_buffer_destroy(gpu_buffer_);
        if (nvme_device_) nvme_close(nvme_device_);
    }

    /**
     * Submit NVMe read command (host submission to GPU memory)
     */
    void submit_read_command(uint64_t lba) {
        NvmeCmd cmd{};
        cmd.opc = OPC_NVM_READ;
        cmd.cid = cmd_id_++;
        cmd.nsid = 1;

        // Set PRP for 4KB transfer
        cmd.prp1 = gpu_buffer_->iova;
        cmd.prp2 = 0;  // 4KB fits in single page

        // LBA and block count
        cmd.cdw10 = static_cast<uint32_t>(lba & 0xFFFFFFFF);
        cmd.cdw11 = static_cast<uint32_t>(lba >> 32);
        cmd.cdw12 = 0;  // 1 block (0-based count)

        // Submit to SQ
        NvmeCmd* sq_entry = reinterpret_cast<NvmeCmd*>(
            static_cast<char*>(iosq_->vaddr) +
            (iosq_->tail * iosq_->entry_size)
        );
        memcpy(sq_entry, &cmd, sizeof(NvmeCmd));

        // Update tail
        iosq_->tail = (iosq_->tail + 1) % iosq_->entries;
        *iosq_->db = iosq_->tail;
    }

    /**
     * Poll for completion
     */
    bool poll_completion(uint16_t expected_cid) {
        NvmeCqe* cq_entry = reinterpret_cast<NvmeCqe*>(
            static_cast<char*>(iocq_->vaddr) +
            (iocq_->head * iocq_->entry_size)
        );

        uint8_t phase = cqe_phase(*cq_entry);
        if (phase != iocq_->phase) {
            return false;  // No new completion
        }

        // Got completion
        if (cq_entry->cid != expected_cid) {
            fprintf(stderr, "CID mismatch: expected %u, got %u\n",
                    expected_cid, cq_entry->cid);
            return false;
        }

        uint8_t sct = cqe_sct(*cq_entry);
        uint8_t sc = cqe_sc(*cq_entry);

        if (sct != 0 || sc != 0) {
            fprintf(stderr, "NVMe error: SCT=%u, SC=%u\n", sct, sc);
            return false;
        }

        // Update head
        iocq_->head = (iocq_->head + 1) % iocq_->entries;
        if (iocq_->head == 0) {
            iocq_->phase ^= 1;
        }
        *iocq_->db = iocq_->head;

        return true;
    }

    /**
     * Benchmark single 4KB read with GPU sum
     */
    ReadResult benchmark_read_and_sum(uint64_t lba) {
        ReadResult result;
        Timer total_timer, component_timer;

        total_timer.start();

        // 1. Build and submit command
        component_timer.start();
        uint16_t cid = cmd_id_;
        submit_read_command(lba);
        component_timer.stop();
        result.command_build_ns = component_timer.elapsed_ns();
        result.submission_ns = component_timer.elapsed_ns();

        // 2. Poll for completion
        component_timer.start();
        while (!poll_completion(cid)) {
            // Busy wait (could use interrupts in production)
        }
        component_timer.stop();
        result.completion_ns = component_timer.elapsed_ns();

        // 3. GPU sum operation
        perf_common::CudaTimer gpu_timer;
        gpu_timer.start(stream_);
        launch_sum_4kb(gpu_buffer_->addr, d_sum_result_, stream_);
        gpu_timer.stop(stream_);
        cudaStreamSynchronize(stream_);

        result.kernel_launch_ns = gpu_timer.elapsed_ns();

        total_timer.stop();
        result.total_ns = total_timer.elapsed_ns();
        result.success = true;

        return result;
    }

    /**
     * Get the sum result from GPU
     */
    uint32_t get_sum_result() {
        uint32_t h_result = 0;
        cudaMemcpy(&h_result, d_sum_result_, sizeof(uint32_t), cudaMemcpyDeviceToHost);
        return h_result;
    }

    /**
     * Run benchmark iterations
     */
    void run_benchmark(uint64_t num_iterations, uint64_t start_lba) {
        std::vector<ReadResult> results;
        results.reserve(num_iterations);

        printf("Running GDS benchmark: %lu iterations\n", num_iterations);
        printf("Reading from LBA %lu (4KB blocks)\n\n", start_lba);

        // Warm-up
        printf("Warming up (100 iterations)...\n");
        for (int i = 0; i < 100; ++i) {
            benchmark_read_and_sum(start_lba + (i % 8));
        }

        // Actual benchmark
        printf("Running benchmark...\n");
        for (uint64_t i = 0; i < num_iterations; ++i) {
            uint64_t lba = start_lba + (i % 8);  // Cycle through 8 blocks
            results.push_back(benchmark_read_and_sum(lba));

            if ((i + 1) % 1000 == 0) {
                printf("  Completed %lu / %lu iterations\r", i + 1, num_iterations);
                fflush(stdout);
            }
        }
        printf("\n\nBenchmark completed.\n\n");

        // Calculate statistics
        print_statistics(results);
    }

private:
    void print_statistics(const std::vector<ReadResult>& results) {
        std::vector<double> latencies;
        latencies.reserve(results.size());

        double sum_cmd_build = 0, sum_completion = 0, sum_kernel = 0;

        for (const auto& r : results) {
            latencies.push_back(r.total_ns / 1000.0);  // Convert to μs
            sum_cmd_build += r.command_build_ns / 1000.0;
            sum_completion += r.completion_ns / 1000.0;
            sum_kernel += r.kernel_launch_ns / 1000.0;
        }

        std::sort(latencies.begin(), latencies.end());

        double mean = std::accumulate(latencies.begin(), latencies.end(), 0.0) / latencies.size();
        double p50 = latencies[latencies.size() / 2];
        double p95 = latencies[static_cast<size_t>(latencies.size() * 0.95)];
        double p99 = latencies[static_cast<size_t>(latencies.size() * 0.99)];
        double min = latencies.front();
        double max = latencies.back();

        printf("╔═══════════════════════════════════════════════════╗\n");
        printf("║  GPUDirect Storage (GDS) Benchmark Results       ║\n");
        printf("║  Host Command Submission + GPU Processing        ║\n");
        printf("╠═══════════════════════════════════════════════════╣\n");
        printf("║ Latency Statistics (μs)                           ║\n");
        printf("╟───────────────────────────────────────────────────╢\n");
        printf("║ Mean:       %8.2f μs                           ║\n", mean);
        printf("║ Median:     %8.2f μs                           ║\n", p50);
        printf("║ P95:        %8.2f μs                           ║\n", p95);
        printf("║ P99:        %8.2f μs                           ║\n", p99);
        printf("║ Min:        %8.2f μs                           ║\n", min);
        printf("║ Max:        %8.2f μs                           ║\n", max);
        printf("╟───────────────────────────────────────────────────╢\n");
        printf("║ Throughput                                        ║\n");
        printf("╟───────────────────────────────────────────────────╢\n");
        printf("║ IOPS:       %8.0f ops/sec                     ║\n", 1000000.0 / mean);
        printf("║ Bandwidth:  %8.2f MB/s (4KB blocks)           ║\n",
               (1000000.0 / mean) * 4096 / (1024 * 1024));
        printf("╚═══════════════════════════════════════════════════╝\n\n");

        printf("Component Breakdown (average μs):\n");
        printf("┌─────────────────────────┬──────────┐\n");
        printf("│ Component               │   Time   │\n");
        printf("├─────────────────────────┼──────────┤\n");
        printf("│ Command Build/Submit    │  %6.2f  │\n", sum_cmd_build / results.size());
        printf("│ Completion Poll         │  %6.2f  │\n", sum_completion / results.size());
        printf("│ GPU Sum Kernel          │  %6.2f  │\n", sum_kernel / results.size());
        printf("└─────────────────────────┴──────────┘\n");
    }
};

/**
 * Main function for GDS benchmark
 */
int main(int argc, char** argv) {
    const char* nvme_bdf = "0000:01:00.0";  // Default BDF
    uint64_t num_iterations = 10000;
    uint64_t start_lba = 0;

    // Parse command line arguments
    if (argc > 1) {
        nvme_bdf = argv[1];
    }
    if (argc > 2) {
        num_iterations = std::stoull(argv[2]);
    }
    if (argc > 3) {
        start_lba = std::stoull(argv[3]);
    }

    printf("╔═══════════════════════════════════════════════════╗\n");
    printf("║  GPUDirect Storage (GDS) Performance Benchmark   ║\n");
    printf("║  4KB Read: Host Submission + GPU Processing      ║\n");
    printf("╚═══════════════════════════════════════════════════╝\n\n");

    printf("Configuration:\n");
    printf("  NVMe Device: %s\n", nvme_bdf);
    printf("  Iterations:  %lu\n", num_iterations);
    printf("  Start LBA:   %lu\n\n", start_lba);

    try {
        GDSBenchmark benchmark(nvme_bdf);
        benchmark.run_benchmark(num_iterations, start_lba);
    } catch (const std::exception& e) {
        fprintf(stderr, "Error: %s\n", e.what());
        return 1;
    }

    return 0;
}
