/**
 * @file io.h
 * @brief Unified NVMe I/O interface supporting both runtime and compile-time polymorphism
 * 
 * Provides two complementary I/O abstractions:
 * - IOInterface: Runtime polymorphism for dynamic dispatch (host-only)
 * - IO<T>: CRTP template for zero-overhead compile-time dispatch (host+GPU)
 * Both support doorbell modes (MMIO, DBC daemon, DBC hardware) and async types.
 */

#pragma once
#include "memory/memory_types.h"
#include "mapper/mapper_host.h"
#include "doorbell/nvme_doorbell.h"
#include "io/io_impl.h"
#include "nvme_types.h"
#include "cuda_utils.h"

// ============================================================================
// Host-Only Virtual Interface (Runtime Polymorphism)
// ============================================================================
// Enables dynamic dispatch for different memory types (host pageable, CUDA pinned, GPU)
// Used when I/O implementation must be selected at runtime based on configuration

class IOInterface {
public:
    IOInterface() = default;
    virtual ~IOInterface() = default;
    IOInterface(const IOInterface&) = delete;
    IOInterface& operator=(const IOInterface&) = delete;

    /// Submit NVMe command with runtime-selected doorbell mode
    /// @param doorbell nullptr=immediate MMIO, non-null=deferred (daemon/DBC)
    /// @return Command ID on success, NVME_CID_QUEUE_FULL if queue full
    virtual uint16_t submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, uint32_t nsid,
                                   uint64_t slba, uint32_t lba_size,
                                   DmaBuf* b, size_t bytes) = 0;

    /// Poll for command completion with configurable blocking behavior
    /// @param async_type SYNC=block until completion, ASYNC=return immediately if no completion
    /// @param iosq Optional submission queue to update SQ head from CQE
    /// @return NVMe status (success/error code from completion queue)
    virtual NvmeStatus poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         uint16_t* out_cid,
                                         PollResult* out_poll_result = nullptr,
                                         uint32_t timeout_us = 0,
                                         Queue* iosq = nullptr) = 0;
};

// ============================================================================
// CRTP Base Class (Compile-Time Polymorphism, Host and GPU)  
// ============================================================================
// Zero-overhead template dispatch for performance-critical GPU kernels and host code
// Enables __device__ __host__ functions with compile-time doorbell/async type selection

template<typename T>
class IO : public IOInterface {
public:
    /// Submit with compile-time command and doorbell type selection (zero-overhead)
    /// @tparam cmd READ/WRITE command type (compiled into instruction stream)
    /// @tparam DoorbellT MMIO/DBC doorbell implementation (no runtime dispatch)
    template<CommandType cmd, typename DoorbellT>
    __device__ __host__ inline uint16_t submit(Queue* iosq, uint32_t nsid,
                                uint64_t slba, uint32_t lba_size,
                                DmaBuf* b, size_t bytes) {
        return static_cast<T*>(this)->template submit<cmd, DoorbellT>(iosq, nsid, slba, lba_size, b, bytes);
    }

    /// Poll with compile-time async behavior selection (eliminates branching)
    /// @tparam async_type SYNC/ASYNC compiled into control flow (no runtime check)
    template<AsyncType async_type>
    __device__ __host__ inline NvmeStatus poll_completion(Queue* iocq, uint16_t* out_cid,
                                      PollResult* out_poll_result = nullptr,
                                      uint32_t timeout_us = 0) {
        return static_cast<T*>(this)->template poll_completion<async_type>(iocq, out_cid, out_poll_result, timeout_us);
    }

    // ========================================================================
    // Direct Queue Operations (replaces QueueIO functionality)
    // ========================================================================
    // Low-level queue manipulation for GPU kernels that bypass buffer management
    // Direct PRP addressing - caller handles memory mapping and page lists

    /// Submit READ command directly to queue (bypasses buffer management)
    /// @param prp1 First physical region page (or PRP list pointer for >2 pages)
    /// @param prp2 Second page address or 0 for single-page transfers
    /// @return Command ID or NVME_CID_QUEUE_FULL if no slots available
    template<typename QueueT>
    __device__ __host__ static inline uint16_t submit_read(
        QueueT* queue, uint64_t slba, uint16_t nlb,
        uint64_t prp1, uint64_t prp2)
    {
        uint16_t cid;
        uint16_t slot = queue->allocate_sq_slot(&cid);
        if (slot == NVME_CID_QUEUE_FULL) return NVME_CID_QUEUE_FULL;

        NvmeCmd cmd;
        nvme_io_impl::build_command(CMD_READ, queue->nsid(), slba, nlb, prp1, prp2, cid, cmd);
        nvme_io_impl::copy_64B(&queue->sq_base()[slot], &cmd);
        #ifdef __CUDA_ARCH__
        __threadfence_system();
        #endif
        queue->ring_sq_doorbell();
        return cid;
    }

    /// Submit WRITE command directly to queue (bypasses buffer management)  
    /// @param nlb Number of logical blocks minus 1 (NVMe 0-based encoding)
    /// @return Command ID or NVME_CID_QUEUE_FULL if submission queue full
    template<typename QueueT>
    __device__ __host__ static inline uint16_t submit_write(
        QueueT* queue, uint64_t slba, uint16_t nlb,
        uint64_t prp1, uint64_t prp2)
    {
        uint16_t cid;
        uint16_t slot = queue->allocate_sq_slot(&cid);
        if (slot == NVME_CID_QUEUE_FULL) return NVME_CID_QUEUE_FULL;

        NvmeCmd cmd;
        nvme_io_impl::build_command(CMD_WRITE, queue->nsid(), slba, nlb, prp1, prp2, cid, cmd);
        nvme_io_impl::copy_64B(&queue->sq_base()[slot], &cmd);
        #ifdef __CUDA_ARCH__
        __threadfence_system();
        #endif
        queue->ring_sq_doorbell();
        return cid;
    }

    /// Poll completion queue for finished commands (non-blocking check)
    /// @param cid Returns command ID of completed operation
    /// @param status Returns NVMe status code (success/error from controller)
    /// @return POLL_SUCCESS if completion found, POLL_EMPTY if no completions ready
    template<typename QueueT>
    __device__ __host__ static inline PollResult poll_completion(
        QueueT* queue, uint16_t* cid, NvmeStatus* status)
    {
        return queue->poll_completion(cid, status);
    }
};
