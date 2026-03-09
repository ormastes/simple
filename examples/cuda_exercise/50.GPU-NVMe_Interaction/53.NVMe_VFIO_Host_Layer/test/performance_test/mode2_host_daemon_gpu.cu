/**
 * @file mode2_host_daemon_gpu.cu
 * @brief Mode 2: Host Command + Daemon polling GPU Memory + GPU Buffer
 *
 * This test benchmarks NVMe I/O where:
 * - CPU builds NVMe commands
 * - CPU writes to GPU memory doorbell buffer (not host memory)
 * - Daemon thread polls GPU memory and writes actual MMIO doorbell
 * - Data buffer in GPU device memory (requires P2P)
 *
 * This mode reduces host-device communication by keeping the doorbell
 * buffer in GPU memory, allowing GPU to potentially monitor progress.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <thread>
#include <chrono>
#include <atomic>
#include <memory>
#include "perf_test_helper.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "helper/nvme_test_helper.h"
#include "nvme_types.h"

using namespace perf_test;

// GPU shadow doorbell structure (in GPU memory)
struct GpuShadowDoorbell {
    uint32_t sq_tail;
    uint32_t cq_head;
    uint32_t should_stop;
    uint32_t padding[13];  // Align to 64 bytes
};

/**
 * @brief Mode 2 performance test implementation
 */
class Mode2PerfTest : public PerfTestBase {
protected:
    NvmeDevice* nvme_device_ = nullptr;
    Queue* iosq_ = nullptr;
    Queue* iocq_ = nullptr;

    // GPU buffer for data
    uint8_t* gpu_data_buffer_ = nullptr;
    uint8_t* pinned_buffer_ = nullptr;  // Pinned host memory for P2P fallback (aligned)
    void* raw_pinned_buffer_ = nullptr;  // Original pinned allocation for cleanup
    uint64_t gpu_buffer_iova_ = 0;

    // Shadow doorbell buffer (host pinned + device alias)
    GpuShadowDoorbell* gpu_shadow_doorbell_ = nullptr;  ///< Device alias
    GpuShadowDoorbell* host_shadow_copy_ = nullptr;     ///< Host pointer

    // Daemon thread
    std::thread daemon_thread_;
    std::atomic<uint64_t> daemon_polls_{0};
    std::atomic<uint64_t> daemon_writes_{0};

    // P2P support
    bool p2p_supported_ = false;

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

        // Allocate GPU data buffer
        cudaMalloc(&gpu_data_buffer_, chunk_size);

        // Allocate shadow doorbell in pinned host memory and get device alias
        CUDA_CHECK(cudaHostAlloc(&host_shadow_copy_, sizeof(GpuShadowDoorbell),
                                 cudaHostAllocMapped));
        memset(host_shadow_copy_, 0, sizeof(GpuShadowDoorbell));
        void* dev_alias = nullptr;
        CUDA_CHECK(cudaHostGetDevicePointer(&dev_alias, host_shadow_copy_, 0));
        gpu_shadow_doorbell_ = static_cast<GpuShadowDoorbell*>(dev_alias);

        // Use pinned memory for data buffer (P2P fallback when GPU P2P not available)
        // Allocate extra space to ensure 4096-byte alignment
        CUDA_CHECK(cudaHostAlloc(&raw_pinned_buffer_, chunk_size + 4096, cudaHostAllocDefault));
        // Align to 4096 bytes
        uintptr_t addr = reinterpret_cast<uintptr_t>(raw_pinned_buffer_);
        uintptr_t aligned_addr = (addr + 4095) & ~4095ULL;
        pinned_buffer_ = reinterpret_cast<uint8_t*>(aligned_addr);

        // Map pinned buffer to IOVA for NVMe DMA
        int ret = host_map_iova(pinned_buffer_, chunk_size, &gpu_buffer_iova_);
        ASSERT_EQ(ret, 0) << "Failed to map pinned buffer to IOVA";

        // Note: In production, would use nvme_gpu_create_cuda_pinned_consecutive_buffer
        // which handles P2P fallback automatically. For testing, we use explicit pinned memory.

        // Start daemon thread
        start_daemon();
    }

    void TearDown() override {
        // Stop daemon
        if (daemon_thread_.joinable()) {
            host_shadow_copy_->should_stop = 1;
            // Copy stop signal to GPU
            cudaMemcpy(&gpu_shadow_doorbell_->should_stop, &host_shadow_copy_->should_stop,
                      sizeof(uint32_t), cudaMemcpyHostToDevice);
            daemon_thread_.join();
        }

        // Clean up CUDA resources
        if (pinned_buffer_ && gpu_buffer_iova_) {
            host_unmap_iova(pinned_buffer_, chunk_size, gpu_buffer_iova_);
        }
        if (raw_pinned_buffer_) cudaFreeHost(raw_pinned_buffer_);
        if (gpu_data_buffer_) cudaFree(gpu_data_buffer_);
        if (host_shadow_copy_) cudaFreeHost(host_shadow_copy_);
        if (host_shadow_copy_) cudaFreeHost(host_shadow_copy_);

        // Close device
        if (nvme_device_) nvme_close(nvme_device_);

        PerfTestBase::TearDown();
    }

    void start_daemon() {
        daemon_thread_ = std::thread([this]() {
            // Set CUDA device for this thread
            cudaSetDevice(0);

            uint32_t last_tail = 0;
            GpuShadowDoorbell local_copy{};
            const auto poll_interval = std::chrono::microseconds(1);  // Reduce to 1us for better responsiveness

            while (true) {
                daemon_polls_++;

                // Directly read host-pinned shadow (GPU alias points here)
                local_copy = *host_shadow_copy_;

                // Check for stop signal
                if (local_copy.should_stop) {
                    break;
                }

                // Check if shadow doorbell changed
                if (local_copy.sq_tail != last_tail) {
                    // Debug output - print more info, including during main benchmark
                    if (daemon_writes_ < 10 || (daemon_writes_ >= 10 && daemon_writes_ < 20)) {
                        printf("[DAEMON write %lu] tail %u -> %u, iosq_->head=%u, doorbell @ %p\n",
                               daemon_writes_.load(), last_tail, local_copy.sq_tail, iosq_->head, (void*)iosq_->db);
                    }

                    // Memory fence before writing doorbell
                    std::atomic_thread_fence(std::memory_order_release);

                    // Write actual MMIO doorbell
                    *(iosq_->db) = local_copy.sq_tail;

                    // Memory fence after writing doorbell
                    std::atomic_thread_fence(std::memory_order_seq_cst);

                    daemon_writes_++;
                    last_tail = local_copy.sq_tail;
                }

                // Very brief sleep to reduce CPU usage while staying responsive
                std::this_thread::sleep_for(poll_interval);
            }
        });
    }

    uint16_t submit_command_with_gpu_shadow(uint64_t lba) {
        // Properly allocate queue slot first
        uint32_t next_tail = (current_tail_ + 1) % queue_size_;

        // Check if queue is full (next tail would equal head)
        // Use acquire fence and volatile read to ensure we see the latest head value
        std::atomic_thread_fence(std::memory_order_acquire);
        uint32_t current_head = *reinterpret_cast<volatile uint32_t*>(&iosq_->head);
        if (next_tail == current_head) {
            printf("ERROR: Queue is full, cannot submit command (tail=%u would equal head=%u)\n",
                   next_tail, current_head);
            return NVME_CID_QUEUE_FULL;
        }

        // Allocate slot and CID (use current tail as both slot and CID)
        uint16_t slot = current_tail_;
        uint16_t cid = current_tail_;

        // Build NVMe read command (CPU builds command)
        NvmeCmd cmd{};
        cmd.opc = 0x02;  // NVM Read
        cmd.nsid = 1;
        cmd.cid = cid;  // Use the allocated CID
        cmd.prp1 = gpu_buffer_iova_;  // GPU buffer IOVA
        cmd.prp2 = 0;
        cmd.cdw10 = lba & 0xFFFFFFFF;
        cmd.cdw11 = (lba >> 32) & 0xFFFFFFFF;
        cmd.cdw12 = (chunk_size / lba_size_ - 1);  // Number of blocks - 1

        // Debug: print command details for first few commands in warmup and main
        static int cmd_count = 0;
        cmd_count++;
        if (cmd_count <= 5 || (cmd_count > 10 && cmd_count <= 15)) {
            printf("[CMD %d] slot=%u, cid=%u, lba=%lu, prp1=0x%lx, blocks=%u\n",
                   cmd_count, slot, cid, lba, gpu_buffer_iova_, (chunk_size / lba_size_));
        }

        // Submit to queue using the allocated slot
        NvmeCmd* sq_base = (NvmeCmd*)iosq_->vaddr;
        memcpy(&sq_base[slot], &cmd, sizeof(NvmeCmd));

        // Ensure command is written to memory before updating shadow doorbell
        std::atomic_thread_fence(std::memory_order_release);

        // Update tail to next position
        current_tail_ = next_tail;

        // Update shadow doorbell (host-pinned, GPU-visible)
        host_shadow_copy_->sq_tail = next_tail;
        std::atomic_thread_fence(std::memory_order_release);

        // Give daemon thread a brief moment to detect the change and write doorbell
        // This is necessary because the daemon polls at 1us intervals
        std::this_thread::sleep_for(std::chrono::microseconds(10));

        // Daemon will detect change and write MMIO doorbell
        return cmd.cid;  // Return the command ID
    }

    bool poll_completion() {
        volatile NvmeCqe* cq_base = (volatile NvmeCqe*)iocq_->vaddr;
        uint32_t head = iocq_->head;
        uint8_t expected_phase = iocq_->phase;

        static int poll_count = 0;
        static int failure_count = 0;
        poll_count++;
        bool debug_this_poll = (poll_count <= 5) || (failure_count > 0 && failure_count <= 5);

        if (debug_this_poll) {
            printf("[POLL %d] Starting poll: head=%u, expected_phase=%u, iosq_->head=%u\n",
                   poll_count, head, expected_phase, iosq_->head);
        }

        // Poll for completion (increase attempts for daemon latency)
        bool found = false;
        uint16_t last_status_p = 0;
        for (int attempts = 0; attempts < 500000; attempts++) {
            // Read status_p field (contains phase bit in bit 0)
            uint16_t status_p = cq_base[head].status_p;
            uint8_t phase = status_p & 0x1;

            // Debug: Print phase info periodically during failures
            if (attempts == 0 || attempts == 100000 || attempts == 499999) {
                if (poll_count > 10 && poll_count <= 15) {
                    printf("[POLL %d attempt %d] head=%u, status_p=0x%x, phase=%u, expected=%u\n",
                           poll_count, attempts, head, status_p, phase, expected_phase);
                }
            }
            last_status_p = status_p;

            if (phase == expected_phase) {  // Phase bit matches
                if (poll_count > 10 && poll_count <= 15) {
                    printf("[POLL %d] PHASE MATCH but checking more conditions...\n", poll_count);
                }
                // Get submission queue head from CQE
                uint16_t sq_head = cq_base[head].sqhd;

                if (poll_count <= 10) {
                    printf("[POLL %d] COMPLETION FOUND! sq_head=%u, cid=%u, status=%u\n",
                           poll_count, sq_head, cq_base[head].cid, (status_p >> 1));
                }

                // Completion available - update head
                head = (head + 1) % iocq_->entries;
                if (head == 0) {
                    iocq_->phase = !expected_phase;  // Flip phase at wrap
                }
                iocq_->head = head;

                // Update submission queue head with memory fence and volatile write
                *reinterpret_cast<volatile uint32_t*>(&iosq_->head) = sq_head;
                std::atomic_thread_fence(std::memory_order_release);

                // Ring CQ doorbell with proper fencing
                std::atomic_thread_fence(std::memory_order_release);
                *(iocq_->db) = head;
                std::atomic_thread_fence(std::memory_order_seq_cst);

                // Update CQ head in shadow buffer for GPU visibility
                host_shadow_copy_->cq_head = head;
                std::atomic_thread_fence(std::memory_order_release);
                found = true;
                break;
            }

            // Brief pause between polls
            __builtin_ia32_pause();
        }

        if (!found) {
            failure_count++;
            if (debug_this_poll || failure_count <= 5) {
                printf("[POLL %d] FAILED - no completion after 500000 attempts (head=%u, phase=%u, last_status_p=0x%x)\n",
                       poll_count, head, expected_phase, last_status_p);
                // Print queue state for debugging
                printf("  Queue state: iosq_->head=%u, iosq_->tail=%u, iocq_->head=%u, current_tail_=%u\n",
                       *reinterpret_cast<volatile uint32_t*>(&iosq_->head),
                       *reinterpret_cast<volatile uint32_t*>(&iosq_->tail),
                       head, current_tail_);
            }
        }

        return found;
    }

    void process_iteration(uint64_t lba, Timer& total_timer) {
        Timer nvme_timer, kernel_timer;

        // 1. Submit NVMe read with GPU shadow doorbell
        nvme_timer.reset();
        uint16_t cid = submit_command_with_gpu_shadow(lba);
        ASSERT_NE(cid, NVME_CID_ERROR) << "Failed to submit command";
        ASSERT_NE(cid, NVME_CID_QUEUE_FULL) << "Queue is full";

        // 2. Poll for completion
        ASSERT_TRUE(poll_completion()) << "NVMe command timeout for CID " << cid;
        double nvme_time = nvme_timer.elapsed_ms();

        // 3. Execute GPU kernel (data already in GPU memory if P2P works)
        kernel_timer.reset();
        execute_gpu_kernel(gpu_data_buffer_, chunk_size, kernel_timer);
        double kernel_time = kernel_timer.elapsed_ms();

        // Record statistics (no memcpy time if P2P works)
        stats.add_iteration(nvme_time, 0.0, kernel_time);
    }
};

TEST_F(Mode2PerfTest, Throughput_4KB) {
    nvme_test::NvmeTestParams config = nvme_test::NvmeTestParams::from_env();
    ASSERT_TRUE(config.is_valid()) << "NVME_BDF not set (set NVME_BDF or NVME_ENV_FALLBACK)";

    std::cout << "\n" << std::string(80, '=') << std::endl;
    std::cout << "Mode 2: Host Command + Daemon (GPU Memory) + GPU Buffer" << std::endl;
    std::cout << "Device: " << config.bdf << std::endl;
    std::cout << "P2P Support: " << (p2p_supported_ ? "YES" : "NO (using fallback)") << std::endl;
    std::cout << "Iterations: " << iterations << std::endl;
    std::cout << "Chunk Size: " << chunk_size << " bytes" << std::endl;
    std::cout << std::string(80, '=') << std::endl;

    // Warmup phase
    std::cout << "Warming up (" << warmup_iterations << " iterations)..." << std::endl;
    run_warmup([this, &config]() {
        Timer timer;
        process_iteration(config.slba, timer);
    });

    // Reset daemon statistics
    daemon_polls_ = 0;
    daemon_writes_ = 0;

    // Main benchmark
    std::cout << "Running benchmark..." << std::endl;
    Timer total_timer;

    for (int i = 0; i < iterations; i++) {
        // Space LBAs properly: increment by number of sectors per chunk to avoid overlap
        uint64_t sectors_per_chunk = chunk_size / lba_size_;
        // Start main benchmark at a different offset to avoid re-using warmup LBAs
        uint64_t lba = config.slba + 10000 + (i % 1000) * sectors_per_chunk;  // Non-overlapping LBAs
        process_iteration(lba, total_timer);

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
    stats.print_summary(ModeNames::MODE_2, chunk_size);

    // Mode 2 characteristics
    std::cout << "\nMode 2 Characteristics:" << std::endl;
    std::cout << "  - CPU builds commands (host-initiated)" << std::endl;
    std::cout << "  - Daemon polls GPU memory for doorbell changes" << std::endl;
    std::cout << "  - GPU buffer allows zero-copy processing (if P2P enabled)" << std::endl;
    std::cout << "  - GPU can potentially monitor progress via shadow buffer" << std::endl;
    std::cout << "  - Trade-off: GPU memory polling overhead vs CPU efficiency" << std::endl;
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
    printf("Mode 2 Test: Host Command + Daemon (GPU Memory) + GPU Buffer\n");
    printf("=============================================================\n");
    printf("GPU Device: %s\n", prop.name);
    printf("=============================================================\n");

    return RUN_ALL_TESTS();
}
