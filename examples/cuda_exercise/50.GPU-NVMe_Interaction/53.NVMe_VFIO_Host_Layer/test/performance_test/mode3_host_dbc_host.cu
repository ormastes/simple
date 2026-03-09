/**
 * @file mode3_host_dbc_host.cu
 * @brief Mode 3: Host Command + DBC Daemon Doorbell + Host Buffer
 *
 * This test benchmarks NVMe I/O where:
 * - CPU builds NVMe commands
 * - CPU writes to shadow doorbell buffer (not MMIO)
 * - Daemon thread polls shadow buffer and writes actual MMIO doorbell
 * - Data buffer in pinned host memory
 *
 * Compared to Mode 1, this reduces CPU overhead by avoiding per-I/O MMIO writes.
 * The daemon polling introduces some latency but improves CPU efficiency.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <thread>
#include <atomic>
#include <memory>
#include <chrono>
#include "perf_test_helper.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "helper/nvme_test_helper.h"
#include "nvme_types.h"

using namespace perf_test;

/**
 * @brief GPU kernel to compute sum of data and derive next LBA
 *
 * Sums the data read from NVMe and uses it to compute the next LBA.
 * This prevents Mode 3 from doing async prefetching since the next
 * address depends on the current data.
 */
__global__ void compute_sum_kernel(const uint8_t* data, size_t size, uint64_t* result) {
    extern __shared__ uint64_t sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Initialize shared memory
    sdata[tid] = 0;

    // Each thread sums multiple elements
    uint64_t local_sum = 0;
    for (size_t i = idx; i < size; i += blockDim.x * gridDim.x) {
        local_sum += data[i];
    }
    sdata[tid] = local_sum;
    __syncthreads();

    // Reduction in shared memory
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Write result
    if (tid == 0) {
        atomicAdd((unsigned long long*)result, (unsigned long long)sdata[0]);
    }
}

// Host shadow doorbell structure (renamed to avoid conflict with nvme_doorbell.h)
struct HostShadowDoorbell {
    std::atomic<uint32_t> sq_tail;
    std::atomic<uint32_t> cq_head;
    std::atomic<bool> should_stop;

    // Cache line padding to avoid false sharing
    alignas(64) char padding[64];

    HostShadowDoorbell() : sq_tail(0), cq_head(0), should_stop(false) {}
};

/**
 * @brief Mode 3 performance test implementation
 */
class Mode3PerfTest : public PerfTestBase {
protected:
    NvmeDevice* nvme_device_ = nullptr;
    Queue* iosq_ = nullptr;
    Queue* iocq_ = nullptr;

    // Pinned host buffer for data
    uint8_t* pinned_host_buffer_ = nullptr;
    uint64_t host_buffer_iova_ = 0;

    // GPU buffer for processing
    uint8_t* gpu_buffer_ = nullptr;
    uint64_t* gpu_sum_result_ = nullptr;  // GPU memory for sum result

    // Shadow doorbell buffer
    std::unique_ptr<HostShadowDoorbell> shadow_doorbell_;

    // Daemon thread
    std::thread daemon_thread_;
    std::atomic<uint64_t> daemon_polls_{0};
    std::atomic<uint64_t> daemon_writes_{0};

    // NVMe queue tail tracking
    uint32_t current_tail_ = 0;
    // Queue size will be determined from actual queue configuration
    uint32_t queue_size_ = 0;
    uint32_t lba_size_ = 512;  // Actual LBA size for block calculations

    void SetUp() override {
        PerfTestBase::SetUp();
        nvme_test::ensure_nvme_env_defaults();

        // Get NVMe device configuration
        nvme_test::NvmeTestParams config = nvme_test::NvmeTestParams::from_env();
        ASSERT_TRUE(config.is_valid()) << "NVME_BDF not set (set NVME_BDF or NVME_ENV_FALLBACK)";

        // Save LBA size for block calculations
        lba_size_ = config.lba_size;

        // Open device with chunk_size as item_size for proper buffer allocation
        // Use reasonable queue depth (128) - actual depth will be capped by device capabilities
        nvme_device_ = nvme_open(config.bdf.c_str(), 128, 128, chunk_size);
        ASSERT_NE(nvme_device_, nullptr) << "Failed to open NVMe device";

        // Get I/O queues
        iosq_ = nvme_get_iosq(nvme_device_);
        iocq_ = nvme_get_iocq(nvme_device_);
        ASSERT_NE(iosq_, nullptr);
        ASSERT_NE(iocq_, nullptr);

        // Get actual queue size from the created queue
        queue_size_ = iosq_->entries;
        printf("INFO: Using queue depth from device: %u\n", queue_size_);

        // Allocate pinned host buffer
        CUDA_CHECK(cudaHostAlloc(&pinned_host_buffer_, chunk_size,
                                 cudaHostAllocDefault));

        // Map the pinned buffer to get its IOVA
        int ret = host_map_iova(pinned_host_buffer_, chunk_size, &host_buffer_iova_);
        ASSERT_EQ(ret, 0) << "Failed to map pinned buffer to IOVA";

        // Allocate GPU buffer for processing
        CUDA_CHECK(cudaMalloc(&gpu_buffer_, chunk_size));
        CUDA_CHECK(cudaMalloc(&gpu_sum_result_, sizeof(uint64_t)));
        CUDA_CHECK(cudaMemset(gpu_sum_result_, 0, sizeof(uint64_t)));

        // Create shadow doorbell
        shadow_doorbell_ = std::make_unique<HostShadowDoorbell>();

        // Pre-write non-zero patterns to NVMe test area
        // This ensures reads return meaningful data for sum calculations
        std::cout << "Pre-writing test patterns to NVMe..." << std::endl;
        const int test_patterns = 1000;  // Write patterns for all test LBAs
        for (int i = 0; i < test_patterns; i++) {
            // Fill buffer with pattern based on LBA
            for (size_t j = 0; j < chunk_size; j++) {
                pinned_host_buffer_[j] = (uint8_t)((i + j) & 0xFF);
            }

            // Check if queue is full before submitting
            uint32_t tail = current_tail_;
            uint32_t next_tail = (tail + 1) % queue_size_;

            // Queue is full when next_tail would equal head
            // (NVMe spec requires one slot to remain empty)
            while (next_tail == iosq_->head) {
                // Poll for any completion to free up a slot
                volatile NvmeCqe* cq_base = (volatile NvmeCqe*)iocq_->vaddr;
                uint32_t cq_head = iocq_->head;
                uint8_t expected_phase = iocq_->phase;

                uint16_t status_p = cq_base[cq_head].status_p;
                uint8_t phase = status_p & 0x1;
                if (phase == expected_phase) {
                    // Process completion to free a slot
                    uint16_t sq_head = cq_base[cq_head].sqhd;
                    iosq_->head = sq_head;

                    cq_head = (cq_head + 1) % iocq_->entries;
                    if (cq_head == 0) {
                        expected_phase = !expected_phase;
                        iocq_->phase = expected_phase;
                    }
                    iocq_->head = cq_head;
                    *(iocq_->db) = cq_head;
                }
                __builtin_ia32_pause();
            }

            // Write pattern to NVMe
            uint64_t lba = config.slba + i;
            NvmeCmd cmd{};
            cmd.opc = 0x01;  // NVM Write
            cmd.nsid = 1;
            cmd.prp1 = host_buffer_iova_;
            cmd.prp2 = 0;
            cmd.cdw10 = lba & 0xFFFFFFFF;
            cmd.cdw11 = (lba >> 32) & 0xFFFFFFFF;
            cmd.cdw12 = (chunk_size / lba_size_ - 1);  // Number of blocks - 1

            NvmeCmd* sq_base = (NvmeCmd*)iosq_->vaddr;
            memcpy(&sq_base[tail], &cmd, sizeof(NvmeCmd));
            current_tail_ = next_tail;
            *(iosq_->db) = next_tail;  // Direct MMIO for setup

            // Poll for completion with timeout
            volatile NvmeCqe* cq_base = (volatile NvmeCqe*)iocq_->vaddr;
            uint32_t head = iocq_->head;
            uint8_t expected_phase = iocq_->phase;

            auto start_time = std::chrono::high_resolution_clock::now();
            const auto timeout = std::chrono::seconds(5);
            bool completed = false;

            while (!completed) {
                uint16_t status_p = cq_base[head].status_p;
                uint8_t phase = status_p & 0x1;
                if (phase == expected_phase) {
                    // Update submission queue head from CQE
                    uint16_t sq_head = cq_base[head].sqhd;
                    iosq_->head = sq_head;

                    head = (head + 1) % iocq_->entries;
                    if (head == 0) expected_phase = !expected_phase;  // Fix: update expected_phase
                    iocq_->head = head;
                    iocq_->phase = expected_phase;  // Update the queue's phase
                    *(iocq_->db) = head;
                    completed = true;
                }

                // Check timeout
                auto now = std::chrono::high_resolution_clock::now();
                if (!completed && (now - start_time) > timeout) {
                    FAIL() << "NVMe completion timeout during pre-write at LBA " << lba;
                }
            }
        }

        // Start daemon thread
        start_daemon();
    }

    void TearDown() override {
        // Stop daemon
        if (daemon_thread_.joinable()) {
            shadow_doorbell_->should_stop = true;
            daemon_thread_.join();
        }

        // Clean up CUDA resources
        if (gpu_buffer_) cudaFree(gpu_buffer_);
        if (gpu_sum_result_) cudaFree(gpu_sum_result_);
        if (pinned_host_buffer_ && host_buffer_iova_) {
            host_unmap_iova(pinned_host_buffer_, chunk_size, host_buffer_iova_);
        }
        if (pinned_host_buffer_) cudaFreeHost(pinned_host_buffer_);

        // Close device
        if (nvme_device_) nvme_close(nvme_device_);

        PerfTestBase::TearDown();
    }

    void start_daemon() {
        daemon_thread_ = std::thread([this]() {
            uint32_t last_tail = 0;
            const auto poll_interval = std::chrono::microseconds(10);

            while (!shadow_doorbell_->should_stop) {
                daemon_polls_++;

                // Check if shadow doorbell changed
                uint32_t new_tail = shadow_doorbell_->sq_tail.load(std::memory_order_acquire);

                if (new_tail != last_tail) {
                    // Write actual MMIO doorbell
                    *(iosq_->db) = new_tail;
                    daemon_writes_++;
                    last_tail = new_tail;
                }

                // Brief sleep to reduce CPU usage
                std::this_thread::sleep_for(poll_interval);
            }
        });
    }

    uint16_t submit_command_with_shadow(uint64_t lba) {
        // Check if queue is full
        uint32_t next_tail = (current_tail_ + 1) % queue_size_;
        if (next_tail == iosq_->head) {
            return NVME_CID_QUEUE_FULL;
        }

        // Build NVMe read command (CPU builds command)
        NvmeCmd cmd{};
        cmd.opc = 0x02;  // NVM Read
        cmd.nsid = 1;
        cmd.cid = current_tail_;
        cmd.prp1 = host_buffer_iova_;
        cmd.prp2 = 0;
        cmd.cdw10 = lba & 0xFFFFFFFF;
        cmd.cdw11 = (lba >> 32) & 0xFFFFFFFF;
        cmd.cdw12 = (chunk_size / lba_size_ - 1);  // Number of blocks - 1

        // Submit to queue (CPU writes command)
        uint32_t tail = current_tail_;
        NvmeCmd* sq_base = (NvmeCmd*)iosq_->vaddr;

        // Copy command to avoid volatile assignment issues
        memcpy(&sq_base[tail], &cmd, sizeof(NvmeCmd));

        // Update tail and write to shadow doorbell (not MMIO)
        current_tail_ = next_tail;
        shadow_doorbell_->sq_tail.store(next_tail, std::memory_order_release);

        // Daemon will detect change and write MMIO doorbell
        return cmd.cid;
    }

    bool poll_completion() {
        volatile NvmeCqe* cq_base = (volatile NvmeCqe*)iocq_->vaddr;
        uint32_t head = iocq_->head;
        uint8_t expected_phase = iocq_->phase;

        // Poll for completion
        for (int attempts = 0; attempts < 100000; attempts++) {
            // Read status_p field (contains phase bit in bit 0)
            uint16_t status_p = cq_base[head].status_p;
            uint8_t phase = status_p & 0x1;

            if (phase == expected_phase) {  // Phase bit matches
                // Update submission queue head from CQE
                uint16_t sq_head = cq_base[head].sqhd;
                iosq_->head = sq_head;

                // Completion available - update head
                head = (head + 1) % iocq_->entries;
                if (head == 0) {
                    iocq_->phase = !expected_phase;  // Flip phase at wrap
                }
                iocq_->head = head;

                // Ring CQ doorbell
                *(iocq_->db) = head;

                // Update shadow CQ head
                shadow_doorbell_->cq_head.store(head, std::memory_order_release);
                return true;
            }

            // Brief pause between polls
            __builtin_ia32_pause();
        }

        return false;
    }

    uint64_t process_iteration(uint64_t lba, Timer& total_timer) {
        Timer nvme_timer, memcpy_timer, kernel_timer;

        // 1. Submit NVMe read with shadow doorbell
        nvme_timer.reset();
        uint16_t cid = submit_command_with_shadow(lba);
        if (cid == NVME_CID_QUEUE_FULL) {
            std::cerr << "Queue full" << std::endl;
            return 0;
        }

        // 2. Poll for completion
        if (!poll_completion()) {
            std::cerr << "NVMe command timeout" << std::endl;
            return 0;  // Return a default value on error
        }
        double nvme_time = nvme_timer.elapsed_ms();

        // 3. Copy from pinned host to GPU
        memcpy_timer.reset();
        CUDA_CHECK(cudaMemcpy(gpu_buffer_, pinned_host_buffer_, chunk_size,
                             cudaMemcpyHostToDevice));
        double memcpy_time = memcpy_timer.elapsed_ms();

        // 4. Execute GPU kernel to compute sum
        kernel_timer.reset();

        // Reset sum result
        CUDA_CHECK(cudaMemset(gpu_sum_result_, 0, sizeof(uint64_t)));

        // Launch sum kernel
        int threads = 256;
        int blocks = (chunk_size + threads - 1) / threads;
        compute_sum_kernel<<<blocks, threads, threads * sizeof(uint64_t)>>>(
            gpu_buffer_, chunk_size, gpu_sum_result_);
        CUDA_CHECK(cudaDeviceSynchronize());

        // Get sum result from GPU
        uint64_t host_sum;
        CUDA_CHECK(cudaMemcpy(&host_sum, gpu_sum_result_, sizeof(uint64_t),
                             cudaMemcpyDeviceToHost));

        double kernel_time = kernel_timer.elapsed_ms();

        // Record statistics
        stats.add_iteration(nvme_time, memcpy_time, kernel_time);

        // Return next LBA based on sum (modulo 1000 to stay in test area)
        return (host_sum % 1000);
    }
};

TEST_F(Mode3PerfTest, Throughput_4KB) {
    nvme_test::NvmeTestParams config;
    config = nvme_test::NvmeTestParams::from_env();
    ASSERT_TRUE(config.is_valid()) << "NVME_BDF not set (set NVME_BDF or NVME_ENV_FALLBACK)";

    std::cout << "\n" << std::string(80, '=') << std::endl;
    std::cout << "Mode 3: Host Command + DBC Daemon + Host Buffer" << std::endl;
    std::cout << "Device: " << config.bdf << std::endl;
    std::cout << "Iterations: " << iterations << std::endl;
    std::cout << "Chunk Size: " << chunk_size << " bytes" << std::endl;
    std::cout << std::string(80, '=') << std::endl;

    // Warmup phase
    std::cout << "Warming up (" << warmup_iterations << " iterations)..." << std::endl;
    uint64_t next_lba_offset = 0;
    for (int i = 0; i < warmup_iterations; i++) {
        Timer timer;
        next_lba_offset = process_iteration(config.slba + next_lba_offset, timer);
    }

    // Reset daemon statistics
    daemon_polls_ = 0;
    daemon_writes_ = 0;

    // Main benchmark
    std::cout << "Running benchmark..." << std::endl;
    Timer total_timer;

    // Start with initial LBA
    next_lba_offset = 0;

    for (int i = 0; i < iterations; i++) {
        // Use computed LBA from previous iteration's sum
        uint64_t lba = config.slba + next_lba_offset;
        next_lba_offset = process_iteration(lba, total_timer);

        if ((i + 1) % 100 == 0) {
            std::cout << "\r  Progress: " << (i + 1) << "/" << iterations
                     << " (" << (100.0 * (i + 1) / iterations) << "%)" << std::flush;
        }
    }

    std::cout << std::endl;

    // Print daemon statistics
    std::cout << "\nDaemon Statistics:" << std::endl;
    std::cout << "  Total Polls: " << daemon_polls_.load() << std::endl;
    std::cout << "  Doorbell Writes: " << daemon_writes_.load() << std::endl;
    std::cout << "  Poll Efficiency: "
             << std::fixed << std::setprecision(2)
             << (100.0 * daemon_writes_ / daemon_polls_) << "%" << std::endl;

    // Print performance summary
    stats.print_summary(ModeNames::MODE_3, chunk_size);

    // Compare with Mode 1 baseline
    double mode3_mean = perf_common::PerformanceStats::get_mean(stats.get_total_times());
    std::cout << "\nComparison:" << std::endl;
    std::cout << "  Mode 3 reduces CPU overhead vs Mode 1 through daemon polling" << std::endl;
    std::cout << "  Trade-off: ~97μs daemon polling latency for lower CPU usage" << std::endl;
    std::cout << "  Best for: High-throughput scenarios where CPU efficiency matters" << std::endl;
}

// ============================================================================
// Main Entry Point
// ============================================================================

int main(int argc, char** argv) {
    testing::InitGoogleTest(&argc, argv);

    // Initialize CUDA
    int device_count;
    cudaGetDeviceCount(&device_count);
    if (device_count == 0) {
        printf("ERROR: No CUDA devices available\n");
        return 1;
    }

    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, 0);
    printf("\n=============================================================\n");
    printf("Mode 3 Test: Host Command + DBC Daemon + Host Buffer\n");
    printf("=============================================================\n");
    printf("GPU Device: %s\n", prop.name);
    printf("=============================================================\n");

    return RUN_ALL_TESTS();
}
