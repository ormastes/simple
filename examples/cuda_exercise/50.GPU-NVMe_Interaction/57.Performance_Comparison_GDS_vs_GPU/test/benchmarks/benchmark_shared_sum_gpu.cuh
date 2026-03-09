/**
 * @file benchmark_shared_sum_gpu.cuh
 * @brief Shared GPU-side loop helper for Modes 4-6.
 *
 * The GPU performs the full iteration loop (single kernel launch),
 * issuing NVMe reads and computing sums with data-dependent addressing.
 */

#pragma once

#include "benchmark_shared_sum.h"
#include "mapper/mapper_gpu.h"
#include "mapper/mapper_gpu_impl.h"  // For nvme_gpu_submit_read
#include <thread>
#include <atomic>
#include <chrono>
#include <cstring>

/**
 * @brief Simple inline daemon for Mode 5 that forwards commands between shadow and VFIO queues
 *
 * The daemon performs:
 * 1. Monitor shadow SQ tail for new commands from GPU
 * 2. Copy new commands from shadow SQ to VFIO SQ
 * 3. Ring MMIO SQ doorbell
 * 4. Monitor VFIO CQ for completions
 * 5. Copy completions from VFIO CQ to shadow CQ
 */
class Mode5Daemon {
public:
    Mode5Daemon(NvmeQueueStruct* queue) : queue_(queue), running_(false), commands_forwarded_(0), completions_forwarded_(0) {}

    void start() {
        if (running_.load()) return;
        running_.store(true);
        thread_ = std::thread(&Mode5Daemon::run, this);
    }

    void stop() {
        running_.store(false);
        if (thread_.joinable()) {
            thread_.join();
        }
    }

    ~Mode5Daemon() { stop(); }

    uint64_t commands_forwarded() const { return commands_forwarded_.load(); }
    uint64_t completions_forwarded() const { return completions_forwarded_.load(); }

private:
    void run() {
        if (!queue_ || !queue_->sq_base || !queue_->cq_base ||
            !queue_->mmio_sq_doorbell) {
            std::fprintf(stderr, "[Mode5Daemon] Invalid queue configuration\n");
            return;
        }

        // Check if we're in direct VFIO access mode (GPU writes directly to VFIO queues)
        // In this case, vfio_sq_base == nullptr and we skip command copying
        bool direct_vfio_mode = (queue_->vfio_sq_base == nullptr);

        // Initialize daemon state from queue struct (shared with GPU via managed memory)
        uint32_t last_sq_tail = queue_->sq_tail;  // Last forwarded SQ tail
        uint32_t last_cq_head = queue_->cq_head;  // Last forwarded CQ head
        uint8_t vfio_cq_phase = queue_->cq_phase; // VFIO CQ phase bit (from queue init)

        // Log daemon mode (minimal output)
        if (direct_vfio_mode) {
            std::fprintf(stderr, "[Mode5Daemon] Direct VFIO mode (no shadow copy)\n");
        } else {
            std::fprintf(stderr, "[Mode5Daemon] Shadow queue mode\n");
        }

        // Drain any stale completions from CQ before starting
        // This handles leftover completions from admin commands during NVMe init
        // In direct mode, cq_base IS the VFIO CQ; otherwise use vfio_cq_base
        // Also extract SQ head from CQE to sync SQ position
        volatile NvmeCqe* cq_for_polling = direct_vfio_mode
            ? queue_->cq_base    // Direct mode: GPU sees VFIO CQ directly
            : queue_->vfio_cq_base;  // Shadow mode: use VFIO CQ for polling

        uint16_t sq_head_from_cqe = 0;
        while (true) {
            uint32_t cq_slot = last_cq_head % queue_->cq_depth;
            volatile NvmeCqe* vfio_cqe = &cq_for_polling[cq_slot];
            uint8_t cqe_phase = (vfio_cqe->status_p) & 1;
            if (cqe_phase != vfio_cq_phase) {
                break;  // No more stale completions
            }
            // Read SQ head from CQE (sqhd field shows where NVMe controller is)
            sq_head_from_cqe = vfio_cqe->sqhd;
            last_cq_head++;
            if ((last_cq_head % queue_->cq_depth) == 0) {
                vfio_cq_phase = !vfio_cq_phase;
            }
            // Ring MMIO CQ doorbell to advance head
            if (queue_->mmio_cq_doorbell) {
                *queue_->mmio_cq_doorbell = last_cq_head % queue_->cq_depth;
            }
        }

        // Sync SQ tail to match NVMe controller's SQ head
        // This ensures we write new commands where the controller expects them
        last_sq_tail = sq_head_from_cqe;
        queue_->sq_tail = sq_head_from_cqe;
        queue_->sq_internal_tail = sq_head_from_cqe;  // Also sync internal tail
        queue_->sq_head = sq_head_from_cqe;  // Initialize sq_head for flow control

        // Sync GPU queue state to match daemon state after draining
        // This ensures GPU and daemon are in sync on CQ position
        queue_->cq_head = last_cq_head;
        queue_->cq_phase = vfio_cq_phase;
        __sync_synchronize();  // Ensure GPU sees updated state

        while (running_.load()) {
            // Check if GPU has written new commands to shadow SQ
            // Use volatile to force fresh read from managed memory
            // GPU writes via atomicAdd, host reads via volatile
            volatile unsigned int* sq_tail_ptr = &queue_->sq_tail;
            uint32_t current_tail = *sq_tail_ptr;
            __sync_synchronize();  // Memory barrier after read

            if (current_tail != last_sq_tail) {
                // Memory barrier to ensure we see GPU's command writes
                __sync_synchronize();

                // Forward new commands from shadow SQ to VFIO SQ
                uint32_t num_new_cmds = (current_tail - last_sq_tail) % queue_->sq_depth;
                if (num_new_cmds == 0 && current_tail != last_sq_tail) {
                    num_new_cmds = queue_->sq_depth;  // Full queue wrap
                }

                if (!direct_vfio_mode) {
                    // Shadow mode: copy commands from shadow SQ to VFIO SQ
                    for (uint32_t i = 0; i < num_new_cmds; i++) {
                        uint32_t slot = (last_sq_tail + i) % queue_->sq_depth;
                        NvmeCmd* src_cmd = &queue_->sq_base[slot];
                        NvmeCmd* dst_cmd = &queue_->vfio_sq_base[slot];
                        std::memcpy(dst_cmd, src_cmd, 64);
                    }
                }
                // Direct mode: GPU already wrote to VFIO SQ, nothing to copy

                // Ring MMIO doorbell with new tail
                uint32_t new_tail = current_tail % queue_->sq_depth;
                *queue_->mmio_sq_doorbell = new_tail;
                asm volatile("mfence" ::: "memory");  // Full memory fence to ensure MMIO is visible

                last_sq_tail = current_tail;
                commands_forwarded_.fetch_add(num_new_cmds);
            }

            if (direct_vfio_mode) {
                // Direct VFIO mode: GPU reads CQ directly and updates queue_->cq_head
                // Daemon just needs to ring MMIO CQ doorbell to tell NVMe we consumed entries
                uint32_t gpu_cq_head = *(volatile uint32_t*)&queue_->cq_head;
                __sync_synchronize();

                // Ring doorbell if GPU has consumed more completions than we've rung for
                if (gpu_cq_head != last_cq_head) {
                    uint32_t db_value = gpu_cq_head % queue_->cq_depth;
                    completions_forwarded_.fetch_add(gpu_cq_head - last_cq_head);
                    last_cq_head = gpu_cq_head;
                    if (queue_->mmio_cq_doorbell) {
                        *queue_->mmio_cq_doorbell = db_value;
                        asm volatile("mfence" ::: "memory");  // Full memory fence to ensure MMIO is visible
                    }
                }
            } else {
                // Shadow mode: daemon polls VFIO CQ and copies completions to shadow CQ
                uint32_t cq_slot = last_cq_head % queue_->cq_depth;
                volatile NvmeCqe* vfio_cqe = &cq_for_polling[cq_slot];
                uint8_t cqe_phase = (vfio_cqe->status_p) & 1;

                if (cqe_phase == vfio_cq_phase) {
                    // Copy completion from VFIO CQ to shadow CQ
                    NvmeCqe shadow_cqe;
                    std::memcpy(&shadow_cqe, const_cast<NvmeCqe*>(vfio_cqe), 16);
                    std::memcpy(&queue_->cq_base[cq_slot], &shadow_cqe, 16);
                    __sync_synchronize();  // Ensure GPU sees the write

                    last_cq_head++;
                    if ((last_cq_head % queue_->cq_depth) == 0) {
                        vfio_cq_phase = !vfio_cq_phase;  // Toggle phase on wrap
                    }

                    // Ring MMIO CQ doorbell to advance head
                    if (queue_->mmio_cq_doorbell) {
                        *queue_->mmio_cq_doorbell = last_cq_head % queue_->cq_depth;
                    }
                    completions_forwarded_.fetch_add(1);
                }
            }

            // Busy poll for maximum performance (remove sleep)
            // std::this_thread::sleep_for(std::chrono::microseconds(1));
        }

    }

    NvmeQueueStruct* queue_;
    std::thread thread_;
    std::atomic<bool> running_;
    std::atomic<uint64_t> commands_forwarded_;
    std::atomic<uint64_t> completions_forwarded_;
};

/**
 * @brief Device function to compute sum of 4KB data (1024 uint32_t elements)
 * @param data Pointer to data buffer
 * @param num_elements Number of elements to sum
 * @return Sum of all elements
 */
__device__ inline uint32_t compute_sum_device(const uint32_t* data, uint32_t num_elements) {
    uint32_t sum = 0;
    for (uint32_t i = 0; i < num_elements; ++i) {
        sum += data[i];
    }
    return sum;
}

/**
 * @brief GPU device function to issue a single NVMe read and poll for completion
 * @param queue GPU queue descriptor
 * @param lba Logical block address to read
 * @param nsid Namespace ID
 * @param buffer_prp PRP/IOVA for data buffer
 * @param lba_size LBA size in bytes
 * @return true on success, false on failure
 */
__device__ inline bool read_once_gpu(
    NvmeQueueStruct* queue,
    uint64_t lba,
    uint32_t nsid,
    uint64_t buffer_prp,
    uint32_t lba_size)
{
    const uint16_t nlb = (4096 / lba_size) - 1;  // 4KB = 8 blocks of 512B
    NvmeStatus status;

    bool success = nvme_gpu_submit_read(
        queue,
        nsid,
        lba,
        nlb,
        buffer_prp,
        0,  // prp2 = 0 for single 4KB read
        &status);

    return success && (status.sc == 0);
}

__global__ void sum_loop_kernel(
    NvmeQueueStruct* queue,
    uint8_t* data_buffer,
    uint64_t buffer_prp,
    uint32_t* out,
    uint64_t start_lba,
    uint32_t nsid,
    uint32_t lba_size,
    uint64_t iterations)
{
    if (blockIdx.x == 0 && threadIdx.x == 0) {
        const uint32_t num_elements = 1024;  // 4KB / sizeof(uint32_t)

        uint64_t current_lba = start_lba;  // Data-dependent LBA chain
        volatile uint32_t* sum_ptr = out;
        uint32_t sum_val = 0;

        for (uint64_t it = 0; it < iterations; ++it) {
            // Step 1: Issue NVMe read at current LBA (data-dependent address)
            bool read_success = read_once_gpu(queue, current_lba, nsid, buffer_prp, lba_size);
            if (!read_success) {
                sum_ptr[0] = 0xFFFFFFFF;  // Mark failure
                return;
            }

            // Step 2: Compute sum of the read data (inline, no child kernel)
            sum_val = compute_sum_device(reinterpret_cast<const uint32_t*>(data_buffer), num_elements);

            // Step 3: Use sum result as next LBA (data-dependent addressing)
            current_lba = sum_val;
        }

        // Store final sum
        sum_ptr[0] = sum_val;
    }
}

inline int run_gpu_loop_benchmark(const ModeDefinition& mode) {
    HostRunContext ctx;
    try {
        init_device_and_pool(mode, ctx);
        allocate_buffers(mode, ctx);
    } catch (const std::exception& ex) {
        std::fprintf(stderr, "[Mode %d] Init failed: %s\n", mode.mode_id, ex.what());
        cleanup_context(ctx);
        return 1;
    }

    std::printf("[Mode %d] %s\n", mode.mode_id, mode.name);
    std::printf("  Iterations (GPU loop): %llu\n", (unsigned long long)ctx.iterations);
    std::printf("  P2P required: %s\n", benchmark_constants::require_p2p_enabled() ? "yes" : "no");
    std::printf("  Buffer IOVA: 0x%llx\n", (unsigned long long)ctx.gpu_buffer_prp);

    if (ctx.gpu_buffer_prp == 0) {
        std::fprintf(stderr, "[Mode %d] ERROR: No P2P/IOVA for GPU buffer; enable P2P.\n", mode.mode_id);
        cleanup_context(ctx);
        return 2;
    }

    // Setup GPU-visible NVMe queue (required for GPU-initiated reads)
    // Use pinned host memory with device mapping for true concurrent CPU/GPU access
    // cudaHostAllocMapped creates memory accessible from both CPU and GPU simultaneously
    void* queue_host_ptr = nullptr;
    CHECK_CUDA(cudaHostAlloc(&queue_host_ptr, sizeof(NvmeQueueStruct),
                             cudaHostAllocMapped | cudaHostAllocPortable));
    std::memset(queue_host_ptr, 0, sizeof(NvmeQueueStruct));

    // Get device pointer for GPU access
    NvmeQueueStruct* gpu_queue_managed = nullptr;
    CHECK_CUDA(cudaHostGetDevicePointer((void**)&gpu_queue_managed, queue_host_ptr, 0));

    // Both pointers point to the same physical memory
    NvmeQueueStruct* queue_for_daemon = reinterpret_cast<NvmeQueueStruct*>(queue_host_ptr);

    int rc = nvme_setup_gpu_queue(ctx.dev, benchmark_constants::get_nvme_bdf_required(), gpu_queue_managed);
    if (rc != 0) {
        std::fprintf(stderr, "[Mode %d] nvme_setup_gpu_queue failed (rc=%d)\n", mode.mode_id, rc);
        std::fprintf(stderr, "\n");
        std::fprintf(stderr, "GPU-initiated I/O (Mode 5/6) requires GPU P2P queue mapping.\n");
        std::fprintf(stderr, "To fix, run one of:\n");
        std::fprintf(stderr, "  1. sudo chmod 666 /dev/gpu_p2p_core  (temporary)\n");
        std::fprintf(stderr, "  2. Add udev rule: KERNEL==\"gpu_p2p_core\", MODE=\"0666\"\n");
        std::fprintf(stderr, "  3. Run benchmark with sudo\n");
        cudaFreeHost(queue_host_ptr);
        cleanup_context(ctx);
        return 2;
    }

    // Start daemon to forward commands between shadow and VFIO queues (Mode 5)
    // The daemon copies commands from shadow SQ to VFIO SQ and rings doorbells
    // Daemon uses host pointer (queue_for_daemon), GPU uses device pointer (gpu_queue_managed)
    // Both point to the same physical pinned memory
    Mode5Daemon daemon(queue_for_daemon);
    if (mode.dbc_daemon) {
        std::printf("[Mode %d] Starting Mode 5 daemon...\n", mode.mode_id);
        daemon.start();
        // Give daemon time to start
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }

    // Zero-initialize GPU buffer and sum
    CHECK_CUDA(cudaMemsetAsync(ctx.gpu_buffer, 0, ctx.chunk_bytes, ctx.stream));
    CHECK_CUDA(cudaMemsetAsync(ctx.gpu_sum, 0, sizeof(uint32_t), ctx.stream));
    CHECK_CUDA(cudaStreamSynchronize(ctx.stream));

    const auto bench_start = std::chrono::steady_clock::now();
    sum_loop_kernel<<<1, 1, 0, ctx.stream>>>(gpu_queue_managed,
                                             ctx.gpu_buffer,
                                             ctx.gpu_buffer_prp,
                                             ctx.gpu_sum,
                                             ctx.start_lba,
                                             benchmark_constants::get_nsid(),
                                             ctx.lba_size,
                                             ctx.iterations);
    CHECK_CUDA(cudaStreamSynchronize(ctx.stream));
    const auto bench_end = std::chrono::steady_clock::now();

    // Stop daemon after kernel completes
    if (mode.dbc_daemon) {
        daemon.stop();
        std::printf("[Mode %d] Daemon stats: %lu commands, %lu completions\n",
                    mode.mode_id, daemon.commands_forwarded(), daemon.completions_forwarded());
    }

    uint32_t host_sum = 0;
    CHECK_CUDA(cudaMemcpy(&host_sum, ctx.gpu_sum, sizeof(uint32_t),
                          cudaMemcpyDeviceToHost));
    if (ctx.staging) {
        std::memcpy(ctx.staging, &host_sum, sizeof(uint32_t));
    }

    if (host_sum == 0xFFFFFFFF) {
        std::fprintf(stderr, "[Mode %d] GPU loop reported failure marker after %llu iterations\n",
                     mode.mode_id, static_cast<unsigned long long>(ctx.iterations));
        cudaFreeHost(queue_host_ptr);
        cleanup_context(ctx);
        return 3;
    }

    const auto elapsed_us = std::chrono::duration_cast<std::chrono::microseconds>(
        bench_end - bench_start).count();
    const double elapsed_sec = static_cast<double>(elapsed_us) / 1e6;
    const double avg_latency_us = static_cast<double>(elapsed_us) / static_cast<double>(ctx.iterations);
    const double iops = static_cast<double>(ctx.iterations) / elapsed_sec;
    const double bandwidth_mbs = (iops * static_cast<double>(ctx.chunk_bytes)) / (1024.0 * 1024.0);

    std::printf("[Mode %d] Complete. Final sum=%u\n", mode.mode_id, host_sum);
    std::printf("[Mode %d] Duration: %.3f s, Average latency: %.2f us\n",
                mode.mode_id, elapsed_sec, avg_latency_us);
    std::printf("[Mode %d] IOPS: %.0f ops/sec, Bandwidth: %.2f MB/s\n",
                mode.mode_id, iops, bandwidth_mbs);

    // Clean up pinned queue memory (not managed by cleanup_context)
    cudaFreeHost(queue_host_ptr);
    cleanup_context(ctx);
    return 0;
}
