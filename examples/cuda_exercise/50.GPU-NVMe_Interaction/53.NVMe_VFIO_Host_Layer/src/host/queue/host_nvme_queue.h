/**
 * @file host_nvme_queue.h
 * @brief Host-side NVMe queue implementation
 *
 * Implements NVMe queue operations for host CPU execution.
 * Optimized for single-threaded, sequential access patterns.
 */

#pragma once

#include <cstdint>
#include <cstdlib>     // For posix_memalign, free
#include <cstring>     // For memset
#include <memory>      // For std::unique_ptr
#include <chrono>      // For timeout functionality
#include "queue/nvme_queue.h"  // For NvmeQueueBase and MmioDoorbell
#include "io/io_impl.h"
#include "io/io.h"  // For IO helper class

/**
 * @brief Host-side NVMe queue (templated by doorbell strategy)
 * @ingroup nvme_queues
 * @tparam DoorbellT Doorbell strategy (MmioDoorbell or ShadowDoorbell)
 *
 * NVMe queue implementation for host CPU. Characteristics:
 * - **Single-threaded**: Sequential SQ tail allocation (no atomics)
 * - **Any-CID polling**: Returns first available completion
 * - **Flexible doorbell**: Supports both MMIO and Shadow doorbell strategies
 * - **Blocking/Non-blocking**: Supports both sync and async polling
 *
 * **Use Cases**:
 * - Module 53: NVMe VFIO Host Layer (MMIO doorbell)
 * - Module 54: CUDA Host Memory (host-initiated I/O)
 * - Module 55.1: Host Queue mode (MMIO doorbell)
 * - Module 55.3: Host DBC Daemon mode (Shadow doorbell)
 *
 * **Performance Characteristics**:
 * - Submit latency: ~200-300ns (MMIO) or ~50-100ns (Shadow)
 * - Poll latency: ~100-200ns (MMIO) or ~30-50ns (Shadow)
 * - Queue full check: O(1)
 *
 * **Example Usage (MMIO doorbell)**:
 * ```cpp
 * // Setup
 * NvmeDevice* dev = nvme_open_device("0000:41:00.0");
 * NvmeQueueStruct* raw_queue = nvme_setup_host_queue(dev, 1, 16, 16);
 *
 * // Create typed queue with MMIO doorbell
 * HostNvmeQueue<MmioDoorbell> queue(
 *     raw_queue->sq_base, raw_queue->cq_base,
 *     16, 16,  // depths
 *     MmioDoorbell(raw_queue->sq_doorbell, raw_queue->cq_doorbell),
 *     1, 512   // nsid, lba_size
 * );
 *
 * // Submit read
 * uint16_t cid = queue.submit_read(1000, 7, prp1, prp2);
 * if (cid == NVME_CID_QUEUE_FULL) { /* handle full queue *\/ }
 *
 * // Poll for completion
 * NvmeStatus status;
 * uint16_t completed_cid;
 * PollResult result = queue.poll_completion(&completed_cid, &status);
 * if (result == POLL_READY && !nvme_io_impl::status_is_error(status)) {
 *     // Success
 * }
 * ```
 *
 * **Example Usage (Shadow doorbell)**:
 * ```cpp
 * // Create shadow doorbell buffers
 * uint32_t* shadow_sq = ...;  // DMA-mapped shadow buffer
 * uint32_t* shadow_cq = ...;
 *
 * // Create typed queue with Shadow doorbell
 * HostNvmeQueue<ShadowDoorbell> queue(
 *     raw_queue->sq_base, raw_queue->cq_base,
 *     16, 16,
 *     ShadowDoorbell(shadow_sq, shadow_cq),
 *     1, 512
 * );
 * // NVMe controller will poll shadow_sq/shadow_cq via DMA
 * ```
 */
template<typename DoorbellT>
class HostNvmeQueue : public NvmeQueue<DoorbellT> {
public:
    using Base = NvmeQueue<DoorbellT>;

    /**
     * @brief Construct host NVMe queue
     *
     * @param sq Submission queue memory
     * @param cq Completion queue memory
     * @param sq_depth SQ depth (power of 2, 2-65536)
     * @param cq_depth CQ depth (power of 2, 2-65536)
     * @param doorbell Doorbell strategy instance (MmioDoorbell or ShadowDoorbell)
     * @param nsid Namespace ID (typically 1)
     * @param lba_size Logical block size in bytes (512 or 4096)
     */
    HostNvmeQueue(NvmeCmd* sq, NvmeCqe* cq,
                  uint16_t sq_depth, uint16_t cq_depth,
                  DoorbellT&& doorbell,
                  uint32_t nsid, uint32_t lba_size)
        : Base(sq, cq, sq_depth, cq_depth, std::move(doorbell), nsid, lba_size) {}

    // ========================================================================
    // Static Factory Method
    // ========================================================================

    /**
     * @brief Create a new HostNvmeQueue with allocated command and completion queues
     *
     * Factory method that allocates memory for submission and completion queues,
     * then creates a new HostNvmeQueue instance.
     *
     * @param sq_depth SQ depth (power of 2, 2-65536)
     * @param cq_depth CQ depth (power of 2, 2-65536)
     * @param doorbell Doorbell strategy instance (MmioDoorbell or ShadowDoorbell)
     * @param nsid Namespace ID (typically 1)
     * @param lba_size Logical block size in bytes (512 or 4096)
     * @return std::unique_ptr to the created queue, or nullptr on failure
     *
     * **Memory Allocation**:
     * - Allocates SQ memory: sq_depth * sizeof(NvmeCmd) bytes
     * - Allocates CQ memory: cq_depth * sizeof(NvmeCqe) bytes
     * - Memory is aligned to page boundary for DMA compatibility
     *
     * **Example Usage**:
     * ```cpp
     * // Create queue with MMIO doorbell
     * auto queue = HostNvmeQueue<MmioDoorbell>::create(
     *     16, 16,  // depths
     *     MmioDoorbell(sq_doorbell_addr, cq_doorbell_addr),
     *     1, 512   // nsid, lba_size
     * );
     *
     * if (!queue) {
     *     // Handle allocation failure
     * }
     *
     * // Use queue for I/O operations
     * uint16_t cid = queue->submit_read(1000, 7, prp1, prp2);
     * ```
     */
    static std::unique_ptr<HostNvmeQueue<DoorbellT>> create(
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

        // Allocate submission queue memory
        // Using posix_memalign for page-aligned allocation (required for DMA)
        void* sq_mem = nullptr;
        void* cq_mem = nullptr;
        const size_t page_size = 4096;

        if (posix_memalign(&sq_mem, page_size, sq_depth * sizeof(NvmeCmd)) != 0) {
            return nullptr;
        }

        if (posix_memalign(&cq_mem, page_size, cq_depth * sizeof(NvmeCqe)) != 0) {
            free(sq_mem);
            return nullptr;
        }

        // Zero initialize the queues
        memset(sq_mem, 0, sq_depth * sizeof(NvmeCmd));
        memset(cq_mem, 0, cq_depth * sizeof(NvmeCqe));

        // Create wrapper class that manages memory lifetime
        class QueueWithMemory : public HostNvmeQueue<DoorbellT> {
            void* sq_mem_;
            void* cq_mem_;
        public:
            QueueWithMemory(void* sq_mem, void* cq_mem,
                           NvmeCmd* sq, NvmeCqe* cq,
                           uint16_t sq_depth, uint16_t cq_depth,
                           DoorbellT&& doorbell,
                           uint32_t nsid, uint32_t lba_size)
                : HostNvmeQueue<DoorbellT>(sq, cq, sq_depth, cq_depth,
                                           std::move(doorbell), nsid, lba_size),
                  sq_mem_(sq_mem), cq_mem_(cq_mem) {}

            ~QueueWithMemory() {
                free(sq_mem_);
                free(cq_mem_);
            }
        };

        return std::unique_ptr<HostNvmeQueue<DoorbellT>>(
            new QueueWithMemory(
                sq_mem, cq_mem,
                static_cast<NvmeCmd*>(sq_mem),
                static_cast<NvmeCqe*>(cq_mem),
                sq_depth, cq_depth,
                std::move(doorbell),
                nsid, lba_size
            )
        );
    }

    // ========================================================================
    // Slot Allocation (Sequential, Single-threaded)
    // ========================================================================

    /**
     * @brief Allocate SQ slot (sequential, non-atomic)
     *
     * Allocates next sequential SQ slot. Checks for queue full condition.
     *
     * @param[out] cid Command ID (equals slot index for simplicity)
     * @return Slot index on success, NVME_CID_QUEUE_FULL if queue is full
     *
     * **Algorithm**:
     * 1. Calculate next tail: (tail + 1) % depth
     * 2. Check if next_tail == head (queue full)
     * 3. Assign slot = tail, cid = tail
     * 4. Advance tail
     *
     * **Thread Safety**: NOT thread-safe. Single-threaded use only.
     */
    inline uint16_t allocate_sq_slot(uint16_t* cid) {
        uint16_t next_tail = (this->sq_tail_ + 1) % this->sq_depth_;

        // Check queue full: next tail catches up to head
        if (next_tail == this->cq_head_) {
            return NVME_CID_QUEUE_FULL;
        }

        *cid = this->sq_tail_;
        uint16_t slot = this->sq_tail_;
        this->sq_tail_ = next_tail;
        return slot;
    }

    // ========================================================================
    // Command Submission
    // ========================================================================

    /**
     * @brief Submit NVMe read command
     *
     * Delegates to IO helper class for command submission.
     *
     * @param slba Starting logical block address
     * @param nlb Number of logical blocks (0-based: 0=1 block, 7=8 blocks)
     * @param prp1 Physical region page 1
     * @param prp2 Physical region page 2 (or PRP list)
     * @return Command ID on success, NVME_CID_QUEUE_FULL if queue full
     *
     * **Implementation**: Delegates to IO<HostNvmeQueue>::submit_read()
     */
    inline uint16_t submit_read(uint64_t slba, uint16_t nlb,
                                     uint64_t prp1, uint64_t prp2) {
        return IO<HostNvmeQueue<DoorbellT>>::submit_read(this, slba, nlb, prp1, prp2);
    }

    /**
     * @brief Submit NVMe write command
     *
     * Delegates to IO helper class for command submission.
     *
     * @param slba Starting logical block address
     * @param nlb Number of logical blocks (0-based)
     * @param prp1 Physical region page 1
     * @param prp2 Physical region page 2 (or PRP list)
     * @return Command ID on success, NVME_CID_QUEUE_FULL if queue full
     *
     * **Implementation**: Delegates to IO<HostNvmeQueue>::submit_write()
     */
    inline uint16_t submit_write(uint64_t slba, uint16_t nlb,
                                      uint64_t prp1, uint64_t prp2) {
        return IO<HostNvmeQueue<DoorbellT>>::submit_write(this, slba, nlb, prp1, prp2);
    }

    // ========================================================================
    // Completion Polling (Any-CID, Host-style)
    // ========================================================================

    /**
     * @brief Poll for any completion (non-blocking)
     *
     * Checks CQ head for new completion. Returns first available completion
     * regardless of CID (any-CID polling).
     *
     * @param[out] cid Command ID of completed command
     * @param[out] status NVMe status (SCT, SC, DNR)
     * @return POLL_READY if completion available, POLL_NOT_READY otherwise
     *
     * **Algorithm**:
     * 1. Check CQE phase bit (cqe_is_new)
     * 2. If no new completion: return POLL_NOT_READY
     * 3. Extract CID and status from CQE
     * 4. Advance CQ head (with phase toggle on wrap)
     * 5. Ring CQ doorbell
     * 6. Return POLL_READY
     *
     * **Comparison to GPU**:
     * - Host: Returns ANY completion (first in CQ)
     * - GPU: Filters by specific CID (may skip other completions)
     */
    inline PollResult poll_completion(uint16_t* cid, NvmeStatus* status) {
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

    /**
     * @brief Synchronous polling with timeout
     *
     * Blocks until completion available or timeout expires.
     *
     * @param[out] cid Command ID of completed command
     * @param[out] status NVMe status
     * @param timeout_us Timeout in microseconds (0 = infinite)
     * @return POLL_READY on success, POLL_TIMEOUT on timeout
     *
     * **Usage**:
     * ```cpp
     * NvmeStatus status;
     * uint16_t cid;
     * if (queue.poll_sync(&cid, &status, 1000000) == POLL_READY) {
     *     // Got completion within 1 second
     * }
     * ```
     */
    inline PollResult poll_sync(uint16_t* cid, NvmeStatus* status,
                                uint32_t timeout_us = 0) {
        if (timeout_us == 0) {
            // Infinite wait
            for (;;) {
                PollResult result = poll_completion(cid, status);
                if (result == POLL_READY) return POLL_READY;
            }
        } else {
            // Timed wait
            auto start = std::chrono::steady_clock::now();
            while (true) {
                PollResult result = poll_completion(cid, status);
                if (result == POLL_READY) return POLL_READY;

                auto now = std::chrono::steady_clock::now();
                auto elapsed_us = std::chrono::duration_cast<std::chrono::microseconds>(
                    now - start).count();
                if (static_cast<uint32_t>(elapsed_us) >= timeout_us) {
                    return POLL_TIMEOUT;
                }
            }
        }
    }
};

// Verify that HostNvmeQueue properly implements the queue interface
template<typename DoorbellT>
struct is_nvme_queue<HostNvmeQueue<DoorbellT>> {
    static constexpr bool value = true;
};

// ============================================================================
// Convenience Type Aliases
// ============================================================================

/// Host queue with MMIO doorbell (REMOVED - MmioDoorbell class removed)
// using HostNvmeQueueMmio = HostNvmeQueue<MmioDoorbell>;  // GPUs cannot access MMIO

/// Host queue with Shadow doorbell (Module 55.3 Host DBC Daemon mode)
using HostNvmeQueueShadow = HostNvmeQueue<ShadowDoorbell>;
