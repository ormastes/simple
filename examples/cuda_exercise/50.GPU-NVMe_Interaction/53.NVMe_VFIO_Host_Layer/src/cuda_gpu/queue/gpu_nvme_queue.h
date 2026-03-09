/**
 * @file gpu_nvme_queue.h
 * @brief GPU-side NVMe queue implementation
 *
 * Implements NVMe queue operations for GPU kernel execution.
 * Optimized for multi-threaded, concurrent access patterns.
 */

#pragma once

#include <cstdint>
#include <memory>      // For std::unique_ptr
#include <cuda_runtime.h>  // For cudaMalloc, cudaFree, cudaMemset
#include "doorbell/nvme_doorbell.h"  // For MmioDoorbell, ShadowDoorbell
#include "queue/nvme_queue.h"     // For NvmeQueueBase (unified header)
#include "io/io_impl.h"
#include "io/io.h"  // For IO helper class
#include "cuda_utils.h"

/**
 * @brief GPU-side NVMe queue
 * @ingroup nvme_queues
 *
 * NVMe queue implementation for GPU kernels. Characteristics:
 * - **Multi-threaded**: Atomic SQ tail allocation (thread-safe)
 * - **CID-filtered polling**: Waits for specific command completion
 * - **Flexible doorbell**: Supports both Shadow (DBC) and MMIO
 * - **Device-only**: Designed for GPU kernel execution
 *
 * **Use Cases**:
 * - Module 55.2: DBC Shadow Doorbell (GPU writes memory buffer)
 * - Module 55.3: Host DBC Daemon (GPU writes shadow, daemon converts to MMIO)
 * - Module 56: GPU Queue with MMIO (GPU direct PCI access)
 *
 * **Performance Characteristics**:
 * - Submit latency: ~50-100ns (atomic + command copy + doorbell)
 * - Poll latency: Variable (depends on filtering, ~100ns per CQE check)
 * - Thread-safe: Multiple threads can submit concurrently
 *
 * **Template Parameters**:
 * @tparam DoorbellT Doorbell strategy (ShadowDoorbell or MmioDoorbell)
 *
 * **Example Usage**:
 * ```cuda
 * __global__ void io_kernel(GpuNvmeQueue<ShadowDoorbell>* queue) {
 *     // Each thread submits independent I/O
 *     uint16_t cid = queue->submit_read(
 *         threadIdx.x * 8,  // slba
 *         7,                // nlb (8 blocks)
 *         prp1, prp2
 *     );
 *
 *     if (cid == NVME_CID_QUEUE_FULL) return;  // Queue full
 *
 *     // Poll for this specific command
 *     NvmeStatus status;
 *     PollResult result = queue->poll_for_cid(cid, &status, 1000000);
 *     if (result == POLL_READY && !nvme_io_impl::status_is_error(status)) {
 *         // Success
 *     }
 * }
 * ```
 */
template<typename DoorbellT>
class GpuNvmeQueue : public NvmeQueue<DoorbellT> {
public:
    using Base = NvmeQueue<DoorbellT>;

    /**
     * @brief Construct GPU NVMe queue
     *
     * @param sq Submission queue memory (GPU-accessible)
     * @param cq Completion queue memory (GPU-accessible)
     * @param sq_depth SQ depth (power of 2, 2-65536)
     * @param cq_depth CQ depth (power of 2, 2-65536)
     * @param doorbell Doorbell strategy instance (Shadow or MMIO)
     * @param nsid Namespace ID (typically 1)
     * @param lba_size Logical block size in bytes (512 or 4096)
     */
    __device__ __host__
    GpuNvmeQueue(NvmeCmd* sq, NvmeCqe* cq,
                 uint16_t sq_depth, uint16_t cq_depth,
                 DoorbellT&& doorbell,
                 uint32_t nsid, uint32_t lba_size)
        : Base(sq, cq, sq_depth, cq_depth, std::move(doorbell), nsid, lba_size) {}

    // ========================================================================
    // Static Factory Method (Host-side)
    // ========================================================================

    /**
     * @brief Create a new GpuNvmeQueue with allocated GPU memory for command and completion queues
     *
     * Factory method that allocates GPU device memory for submission and completion queues,
     * then creates a new GpuNvmeQueue instance. This function should be called from host code
     * to prepare queues that will be used by GPU kernels.
     *
     * @param sq_depth SQ depth (power of 2, 2-65536)
     * @param cq_depth CQ depth (power of 2, 2-65536)
     * @param doorbell Doorbell strategy instance (ShadowDoorbell or MmioDoorbell)
     * @param nsid Namespace ID (typically 1)
     * @param lba_size Logical block size in bytes (512 or 4096)
     * @return std::unique_ptr to the created queue, or nullptr on failure
     *
     * **Memory Allocation**:
     * - Allocates SQ memory on GPU: sq_depth * sizeof(NvmeCmd) bytes
     * - Allocates CQ memory on GPU: cq_depth * sizeof(NvmeCqe) bytes
     * - Memory is allocated using cudaMalloc for GPU device memory
     * - For P2P operations, the allocated memory needs to be mapped separately
     *
     * **Example Usage (Host code)**:
     * ```cpp
     * // Create queue with Shadow doorbell
     * uint32_t* shadow_sq_db, *shadow_cq_db;
     * cudaMallocManaged(&shadow_sq_db, sizeof(uint32_t));
     * cudaMallocManaged(&shadow_cq_db, sizeof(uint32_t));
     *
     * auto h_queue = GpuNvmeQueue<ShadowDoorbell>::create(
     *     16, 16,  // depths
     *     ShadowDoorbell(shadow_sq_db, shadow_cq_db),
     *     1, 512   // nsid, lba_size
     * );
     *
     * if (!h_queue) {
     *     // Handle allocation failure
     * }
     *
     * // Copy queue to device
     * GpuNvmeQueue<ShadowDoorbell>* d_queue;
     * cudaMalloc(&d_queue, sizeof(GpuNvmeQueue<ShadowDoorbell>));
     * cudaMemcpy(d_queue, h_queue.get(), sizeof(GpuNvmeQueue<ShadowDoorbell>),
     *            cudaMemcpyHostToDevice);
     *
     * // Use in kernel
     * io_kernel<<<blocks, threads>>>(d_queue);
     * ```
     *
     * **P2P Mapping Note**:
     * For NVMe DMA operations, the GPU memory needs to be mapped via P2P.
     * This requires additional setup through the P2P kernel module:
     * ```cpp
     * // After allocation, setup P2P mapping
     * CudaP2PTokens tokens;
     * nvme_cuda_query_p2p_tokens(sq_mem, &tokens);
     * // Use tokens with kernel module to establish P2P mapping
     * ```
     */
    static std::unique_ptr<GpuNvmeQueue<DoorbellT>> create(
        uint16_t sq_depth, uint16_t cq_depth,
        DoorbellT doorbell,
        uint32_t nsid, uint32_t lba_size)
    {
        // Validate queue depths (must be power of 2)
        if ((sq_depth & (sq_depth - 1)) != 0 || sq_depth < 2 || sq_depth > 65536) {
            return nullptr;
        }
        if ((cq_depth & (cq_depth - 1)) != 0 || cq_depth < 2 || cq_depth > 65536) {
            return nullptr;
        }

        // Allocate ONE contiguous block for SQ + CQ (reduces allocations and mapping)
        const size_t sq_size = sq_depth * sizeof(NvmeCmd);
        const size_t cq_size = cq_depth * sizeof(NvmeCqe);
        const size_t total_size = sq_size + cq_size;

        void* queue_mem = cuda_calloc<uint8_t>(total_size);
        if (!queue_mem) return nullptr;

        // Split memory into SQ and CQ regions
        NvmeCmd* d_sq = static_cast<NvmeCmd*>(queue_mem);
        NvmeCqe* d_cq = reinterpret_cast<NvmeCqe*>(static_cast<uint8_t*>(queue_mem) + sq_size);

        // Create wrapper class that manages GPU memory lifetime
        class QueueWithGpuMemory : public GpuNvmeQueue<DoorbellT> {
        public:
            QueueWithGpuMemory(NvmeCmd* d_sq, NvmeCqe* d_cq,
                              uint16_t sq_depth, uint16_t cq_depth,
                              DoorbellT&& doorbell,
                              uint32_t nsid, uint32_t lba_size)
                : GpuNvmeQueue<DoorbellT>(d_sq, d_cq, sq_depth, cq_depth,
                                         std::move(doorbell), nsid, lba_size) {}

            ~QueueWithGpuMemory() {
                cuda_free(this->sq_);  // d_sq points to start of single allocation
            }
        };

        // Create host-side queue object that manages GPU memory
        return std::unique_ptr<GpuNvmeQueue<DoorbellT>>(
            new QueueWithGpuMemory(
                d_sq, d_cq,
                sq_depth, cq_depth,
                std::move(doorbell),
                nsid, lba_size
            )
        );
    }

    // ========================================================================
    // Slot Allocation (Atomic, Multi-threaded)
    // ========================================================================

    /**
     * @brief Allocate SQ slot (atomic, thread-safe)
     *
     * Atomically allocates next SQ slot. Safe for concurrent access from
     * multiple threads. Uses atomicAdd() on sq_tail_.
     *
     * @param[out] cid Command ID (equals slot index)
     * @return Slot index on success, NVME_CID_QUEUE_FULL if queue is full
     *
     * **Algorithm**:
     * 1. Atomically fetch-and-add sq_tail
     * 2. Compute slot = old_tail % sq_depth
     * 3. Check if queue is full (compare with cq_head)
     * 4. If full: rollback with atomicSub, return QUEUE_FULL
     * 5. Assign cid = slot
     *
     * **Thread Safety**: FULLY thread-safe via atomic operations
     *
     * **Note**: Queue full check is racy (may allocate slightly past capacity),
     * but NVMe spec allows this (controller will reject if truly full).
     */
    __device__ inline uint16_t allocate_sq_slot(uint16_t* cid) {
        // Atomic fetch-and-add on sq_tail
        uint16_t old_tail = atomicAdd(&this->sq_tail_, 1);
        uint16_t slot = old_tail % this->sq_depth_;

        // Check queue full (racy but safe)
        uint16_t next_tail = (old_tail + 1) % this->sq_depth_;
        if (next_tail == this->cq_head_) {
            // Queue likely full, rollback
            atomicSub(&this->sq_tail_, 1);
            return NVME_CID_QUEUE_FULL;
        }

        *cid = slot;
        return slot;
    }

    // ========================================================================
    // Command Submission
    // ========================================================================

    /**
     * @brief Submit NVMe read command (GPU kernel)
     *
     * Delegates to IO helper class for command submission.
     * Thread-safe for concurrent submissions.
     *
     * @param slba Starting logical block address
     * @param nlb Number of logical blocks (0-based: 0=1 block, 7=8 blocks)
     * @param prp1 Physical region page 1
     * @param prp2 Physical region page 2 (or PRP list)
     * @return Command ID on success, NVME_CID_QUEUE_FULL if queue full
     *
     * **Implementation**: Delegates to IO<GpuNvmeQueue>::submit_read()
     *
     * **Memory Ordering**: IO ensures __threadfence_system() for GPU writes
     */
    __device__ inline uint16_t submit_read(uint64_t slba, uint16_t nlb,
                                                uint64_t prp1, uint64_t prp2) {
        return IO<GpuNvmeQueue<DoorbellT>>::submit_read(this, slba, nlb, prp1, prp2);
    }

    /**
     * @brief Submit NVMe write command (GPU kernel)
     *
     * Delegates to IO helper class for command submission.
     *
     * @param slba Starting logical block address
     * @param nlb Number of logical blocks (0-based)
     * @param prp1 Physical region page 1
     * @param prp2 Physical region page 2 (or PRP list)
     * @return Command ID on success, NVME_CID_QUEUE_FULL if queue full
     *
     * **Implementation**: Delegates to IO<GpuNvmeQueue>::submit_write()
     */
    __device__ inline uint16_t submit_write(uint64_t slba, uint16_t nlb,
                                                 uint64_t prp1, uint64_t prp2) {
        return IO<GpuNvmeQueue<DoorbellT>>::submit_write(this, slba, nlb, prp1, prp2);
    }

    // ========================================================================
    // Completion Polling (CID-Filtered, GPU-style)
    // ========================================================================

    /**
     * @brief Poll for specific command completion (CID-filtered)
     *
     * Polls CQ until the specified command completes. Skips over completions
     * for other commands (they remain unprocessed in CQ).
     *
     * @param target_cid Command ID to wait for
     * @param[out] status NVMe status (SCT, SC, DNR)
     * @param max_iterations Maximum poll iterations (0 = infinite)
     * @return POLL_READY if target_cid completed, POLL_TIMEOUT if exceeded iterations
     *
     * **Algorithm**:
     * 1. Check CQE at cq_head for new completion
     * 2. If CID matches target_cid: extract status, advance head, ring doorbell
     * 3. If CID doesn't match: skip (leave unprocessed for other threads)
     * 4. Repeat until target_cid found or max_iterations reached
     *
     * **Comparison to Host**:
     * - Host: Returns ANY completion (first in CQ)
     * - GPU: Filters by CID (waits for specific command)
     *
     * **Thread Safety**: Multiple threads can poll for different CIDs,
     * but each CID should be polled by only ONE thread (no CID reuse).
     *
     * **Warning**: If multiple threads poll for same CID, only one will
     * receive the completion (race condition).
     */
    __device__ inline PollResult poll_for_cid(uint16_t target_cid,
                                              NvmeStatus* status,
                                              uint32_t max_iterations = 0) {
        uint32_t iterations = 0;

        while (max_iterations == 0 || iterations < max_iterations) {
            NvmeCqe* cqe = &this->cq_base_[this->cq_head_];

            // Check if new completion available
            if (this->cqe_is_new(*cqe)) {
                uint16_t completed_cid = cqe->cid;

                if (completed_cid == target_cid) {
                    // Found our completion
                    this->parse_cqe(*cqe, status);

                    // Advance CQ head
                    this->advance_cq_head();

                    // Ring CQ doorbell
                    this->ring_cq_doorbell();

                    return POLL_READY;
                }
                // else: Skip this completion (belongs to another thread)
            }

            ++iterations;
        }

        return POLL_TIMEOUT;
    }

    /**
     * @brief Poll for any completion (non-CID-filtered, host-like)
     *
     * Returns first available completion regardless of CID.
     * Useful for single-threaded GPU kernels or when order doesn't matter.
     *
     * @param[out] cid Command ID of completed command
     * @param[out] status NVMe status
     * @return POLL_READY if completion available, POLL_NOT_READY otherwise
     *
     * **Use Case**: Simple GPU kernels with sequential I/O, debugging
     */
    __device__ inline PollResult poll_completion(uint16_t* cid, NvmeStatus* status) {
        NvmeCqe* cqe = &this->cq_base_[this->cq_head_];

        // Check if new completion available
        if (!this->cqe_is_new(*cqe)) {
            return POLL_NOT_READY;
        }

        // Extract CID and status
        *cid = cqe->cid;
        this->parse_cqe(*cqe, status);

        // Advance CQ head
        this->advance_cq_head();

        // Ring CQ doorbell
        this->ring_cq_doorbell();

        return POLL_READY;
    }
};

// Verify that GpuNvmeQueue properly implements the queue interface
template<typename DoorbellT>
struct is_nvme_queue<GpuNvmeQueue<DoorbellT>> {
    static constexpr bool value = true;
};

// Common type aliases for convenience
using GpuNvmeQueueShadow = GpuNvmeQueue<ShadowDoorbell>;
using GpuNvmeQueueMmio = GpuNvmeQueue<MmioDoorbell>;
