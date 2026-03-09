/**
 * @file cuda_io_host_mem.h
 * @brief Common definitions and utilities for cuda_io_host_mem
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cuda_runtime_api.h>
#include "memory/memory_pool.h"          // For DmaBuf, Buffer definitions
#include "mapper/mapper_host.h"          // For NvmeDevice, Queue, CommandType, DoorbellType, etc.
#include "io/host_io_host_mem.h"           // For template submit/poll interfaces
#include "io/io.h"                         // For IO base class
#include "memory/cuda_host_memory_buffer.h" // For CUDA host pool implementation

// CUDA host-pinned helpers that operate on host memory buffers.
// Uses unified DmaBuf with BufferKind = BUFFER_KIND_PINNED_HOST

extern "C" {
// Note: Pool management functions (cuda_host_pool_create, cuda_host_pool_acquire, etc.)
// and basic memory functions (cuda_host_alloc, cuda_host_free, etc.) are declared
// in cuda_host_memory_buffer.h

// ============================================================================
// Unified Command Submission API (Module 54.4 - Runtime Dispatch)
// ============================================================================

/// Runtime dispatch version for CUDA host-pinned buffers
/// Identical to host_submit_runtime but explicitly for CUDA host memory
///
/// @param cmd_type Command type (CMD_READ or CMD_WRITE)
/// @param doorbell Doorbell behavior (DOORBELL_DEFERRED, DOORBELL_DEFERRED_EVENTIDX) - MMIO removed
/// @param iosq I/O submission queue
/// @param nsid Namespace ID
/// @param slba Starting logical block address
/// @param lba_size Logical block size in bytes
/// @param b Pre-mapped DMA buffer (CUDA host-pinned memory)
/// @param bytes Number of bytes to transfer (must be multiple of lba_size)
/// @return CID (0-65534) on success, NVME_CID_QUEUE_FULL (0xFFFE) if full, NVME_CID_ERROR (0xFFFF) on error
///
/// Note: This is a thin wrapper around host_submit_runtime() from Module 53
///       CUDA host-pinned memory works seamlessly since it's just pinned system memory
uint16_t cuda_host_submit_runtime(CommandType cmd_type, const DoorbellHandle* doorbell,
                                        Queue* iosq, uint32_t nsid,
                                        uint64_t slba, uint32_t lba_size,
                                        DmaBuf* b, size_t bytes);

// ============================================================================
// Completion Polling API (Module 54.5 - Runtime Dispatch)
// ============================================================================

/// Runtime dispatch version for completion polling
/// Supports both synchronous (blocking) and asynchronous (non-blocking) modes
///
/// @param async_type Polling mode (ASYNC_TYPE_SYNC or ASYNC_TYPE_ASYNC)
/// @param iocq I/O completion queue
/// @param out_cid Pointer to store completed command ID (optional, can be nullptr)
/// @param out_poll_result Pointer to store PollResult (optional for sync, required for async)
/// @param timeout_us Timeout in microseconds (0 = infinite, only used in ASYNC_TYPE_SYNC)
/// @return NvmeStatus with completion status
///
/// Note: This is a thin wrapper around host_poll_completion_runtime() from Module 53
///       Completion polling is independent of buffer type
NvmeStatus cuda_host_poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                              uint16_t* out_cid,
                                              PollResult* out_poll_result = nullptr,
                                              uint32_t timeout_us = 0,
                                              Queue* iosq = nullptr);

} // extern "C"

// ============================================================================
// Template-Based Submit/Poll APIs (Compile-Time Dispatch)
// ============================================================================

/// Template-based submission with compile-time command and doorbell selection
/// Enables compiler optimizations by eliminating runtime branches
///
/// Template parameters:
///   cmd       - Command type (CMD_READ or CMD_WRITE)
///   doorbell  - Doorbell behavior (DOORBELL_DEFERRED, DOORBELL_DEFERRED_EVENTIDX) - MMIO removed
///
/// Runtime parameters:
///   iosq      - I/O submission queue
///   nsid      - Namespace ID
///   slba      - Starting logical block address
///   lba_size  - Logical block size in bytes
///   b         - Pre-mapped DMA buffer (CUDA host-pinned memory)
///   bytes     - Number of bytes to transfer
///
/// Return value:
///   - CID (0-65534) on success
///   - NVME_CID_QUEUE_FULL (0xFFFE) if submission queue is full
///   - NVME_CID_ERROR (0xFFFF) on invalid arguments
///
/// Usage examples:
///   // Compile-time optimized read with immediate doorbell
///   uint16_t cid = cuda_host_submit<CMD_READ, DOORBELL_DEFERRED>(iosq, nsid, slba, lba_size, buf, bytes);
///
///   // Compile-time optimized write with deferred doorbell
///   uint16_t cid = cuda_host_submit<CMD_WRITE, DOORBELL_DEFERRED>(iosq, nsid, slba, lba_size, buf, bytes);
///
///   // Compile-time optimized read with event index optimization
///   uint16_t cid = cuda_host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(iosq, nsid, slba, lba_size, buf, bytes);
///
template<CommandType cmd, DoorbellType doorbell>
uint16_t cuda_host_submit(Queue* iosq, uint32_t nsid,
                                uint64_t slba, uint32_t lba_size,
                                DmaBuf* b, size_t bytes);

/// Template-based polling with compile-time async type selection
/// Enables compiler optimizations by eliminating runtime branches
///
/// Template parameter:
///   async_type - Polling mode (ASYNC_TYPE_SYNC or ASYNC_TYPE_ASYNC)
///
/// Runtime parameters:
///   iocq            - I/O completion queue
///   out_cid         - Pointer to store completed command ID (optional)
///   out_poll_result - Pointer to store PollResult (optional for sync, required for async)
///   timeout_us      - Timeout in microseconds (0 = infinite, only used in ASYNC_TYPE_SYNC)
///
/// Return value (NvmeStatus):
///   - For ASYNC_TYPE_SYNC: Returns valid NvmeStatus when completion ready
///   - For ASYNC_TYPE_ASYNC: Returns NvmeStatus (check out_poll_result for validity)
///
/// Usage examples:
///   // Compile-time optimized blocking poll with infinite wait
///   NvmeStatus status = cuda_host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &cid);
///
///   // Compile-time optimized blocking poll with timeout
///   PollResult result;
///   NvmeStatus status = cuda_host_poll_completion<ASYNC_TYPE_SYNC>(iocq, &cid, &result, 1000000);
///
///   // Compile-time optimized non-blocking poll
///   PollResult result;
///   NvmeStatus status = cuda_host_poll_completion<ASYNC_TYPE_ASYNC>(iocq, &cid, &result);
///
template<AsyncType async_type>
NvmeStatus cuda_host_poll_completion(Queue* iocq, uint16_t* out_cid,
                                      PollResult* out_poll_result = nullptr,
                                      uint32_t timeout_us = 0);

// ============================================================================
// CudaHostIO Class (CRTP Pattern)
// ============================================================================

class CudaHostIO : public IO<CudaHostIO> {
public:
    CudaHostIO() = default;
    ~CudaHostIO() = default;
    CudaHostIO(const CudaHostIO&) = delete;
    CudaHostIO& operator=(const CudaHostIO&) = delete;

    virtual inline uint16_t submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, uint32_t nsid,
                                   uint64_t slba, uint32_t lba_size,
                                   DmaBuf* b, size_t bytes) override {
        return ::cuda_host_submit_runtime(cmd, doorbell, iosq, nsid, slba, lba_size, b, bytes);
    }

    virtual inline NvmeStatus poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         uint16_t* out_cid,
                                         PollResult* out_poll_result = nullptr,
                                         uint32_t timeout_us = 0,
                                         Queue* iosq = nullptr) override {
        return ::cuda_host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us, iosq);
    }

    template<CommandType cmd, DoorbellType doorbell>
    inline uint16_t submit(Queue* iosq, uint32_t nsid,
                                  uint64_t slba, uint32_t lba_size,
                                  DmaBuf* b, size_t bytes) {
        return ::cuda_host_submit<cmd, doorbell>(iosq, nsid, slba, lba_size, b, bytes);
    }

    template<AsyncType async_type>
    inline NvmeStatus poll_completion(Queue* iocq, uint16_t* out_cid,
                                        PollResult* out_poll_result = nullptr,
                                        uint32_t timeout_us = 0) {
        return ::cuda_host_poll_completion<async_type>(iocq, out_cid, out_poll_result, timeout_us);
    }
};

// ============================================================================
// Compatibility Aliases (for code that uses Module 53's interface directly)
// ============================================================================

/// CUDA host memory can also use Module 53's host_submit/host_poll_completion templates
/// directly since CUDA host-pinned memory is just pinned system memory.
/// These are provided by including host_io_host_mem.h which Module 54 already includes.

// Include template implementations
#include "io/cuda_io_host_mem_impl.h"
