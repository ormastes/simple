/**
 * @file cuda_io_gpu_mem.h
 * @brief Common definitions and utilities for cuda_io_gpu_mem
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cuda_runtime_api.h>
#include "mapper/mapper_host.h"      // For Queue, NvmeCmd, CommandType, DoorbellType, etc.
#include "io/io.h"                 // For IO<T> CRTP base class
#include "io/host_io_host_mem.h"   // For host_poll_completion_runtime()
#include "mapper/mapper_gpu.h"     // For CudaP2PTokens and GPU mapper functions

// GPU memory helpers that operate on GPU device memory buffers.
// They require GPU P2P DMA mapping via kernel module for real hardware.

// Forward declarations
// Note: CudaGpuPool is defined in memory_buffer.h as a type alias
struct NvmeDevice;
struct DmaBuf;         // Unified buffer structure from memory_buffer.h
struct IovaSeg;        // IOVA segment structure from memory_buffer.h

// Note: GPU buffers now use the unified DmaBuf structure from memory_buffer.h
// which supports both host and GPU memory types via the BufferKind discriminator.

extern "C" {
// ============================================================================
// GPU Buffer Pool Interface (Module 55.0 - High-Level Public API)
// ============================================================================
//
// Note: Low-level PRP building and CUDA memory helpers are internal implementation
//       details. See cuda_io_gpu_mem_impl.h for those functions.
//       Use the pool APIs below for GPU buffer management.

/// @brief Create GPU device buffer pool with P2P DMA mapping
/// @param d NVMe device handle
/// @param buf_size Size per buffer (page-aligned)
/// @param count Number of buffers
/// @return Pool handle or nullptr on failure
/// @note Requires GPU P2P kernel module
__host__ CudaGpuPool* cuda_gpu_pool_create(NvmeDevice* d, std::size_t buf_size, std::uint16_t count);

/// @brief Acquire buffer from pool (non-blocking)
/// @param p Pool handle
/// @return Buffer or nullptr if pool empty
__host__ DmaBuf* cuda_gpu_pool_acquire(CudaGpuPool* p);

/// @brief Release buffer back to pool
/// @param p Pool handle
/// @param b Buffer to release
__host__ void cuda_gpu_pool_release(CudaGpuPool* p, DmaBuf* b);

/// @brief Destroy pool and free all buffers
/// @param p Pool handle
__host__ void cuda_gpu_pool_destroy(CudaGpuPool* p);

// ============================================================================
// GPU Pinned Consecutive Buffer (Module 55.0.3)
// ============================================================================

/// @brief Create GPU device buffer with P2P DMA mapping
/// @param buffer_size Buffer size (page-aligned)
/// @return Buffer descriptor or nullptr on failure
/// @note Requires kernel module for P2P mapping
__host__ Buffer* cuda_gpu_create_device_consecutive_buffer(std::size_t buffer_size);

/// @brief Destroy GPU device buffer
/// @param b Buffer to destroy
__host__ void cuda_gpu_buffer_destroy(Buffer* b);

// ============================================================================
// Runtime GPU Submit API (Module 55.0.4)
// ============================================================================

/// @brief Submit NVMe command with runtime dispatch
/// @param cmd Command type (CMD_READ/CMD_WRITE)
/// @param doorbell Doorbell type
/// @param iosq I/O submission queue
/// @param nsid Namespace ID
/// @param slba Starting LBA
/// @param lba_size Block size in bytes
/// @param bytes Transfer size
/// @param prp1 First PRP IOVA
/// @param prp2 Second PRP IOVA or PRP list
/// @return CID, NVME_CID_QUEUE_FULL, or NVME_CID_ERROR
__host__ std::uint16_t cuda_submit_runtime(CommandType cmd, DoorbellType doorbell,
                                           Queue* iosq, std::uint32_t nsid,
                                           std::uint64_t slba, std::uint32_t lba_size,
                                           std::size_t bytes,
                                           std::uint64_t prp1, std::uint64_t prp2);

} // extern "C"

// ============================================================================
// Template-Based Submit/Poll APIs (Compile-Time Dispatch)
// ============================================================================

/// @brief Submit NVMe command with compile-time dispatch
/// @tparam cmd Command type (CMD_READ/CMD_WRITE)
/// @tparam doorbell Doorbell type
/// @return CID, NVME_CID_QUEUE_FULL, or NVME_CID_ERROR
template<CommandType cmd, DoorbellType doorbell>
__host__ inline std::uint16_t cuda_submit(Queue* iosq, std::uint32_t nsid,
                                          std::uint64_t slba, std::uint32_t lba_size,
                                          std::size_t bytes,
                                          std::uint64_t prp1, std::uint64_t prp2) {
    return cuda_submit_runtime(cmd, doorbell, iosq, nsid, slba, lba_size, bytes, prp1, prp2);
}

/// @brief Poll completion with compile-time dispatch
/// @tparam async_type Polling mode (ASYNC_TYPE_SYNC/ASYNC_TYPE_ASYNC)
/// @param iocq Completion queue
/// @param out_cid Command ID output
/// @param out_poll_result Poll result output
/// @param timeout_us Timeout in microseconds (0=infinite, sync only)
/// @return NvmeStatus
/// @note Wraps host_poll_completion_runtime (buffer-agnostic)
template<AsyncType async_type>
__host__ inline NvmeStatus cuda_poll_completion(Queue* iocq, std::uint16_t* out_cid,
                                                PollResult* out_poll_result = nullptr,
                                                std::uint32_t timeout_us = 0) {
    return host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us);
}

// ============================================================================
// CudaIO Class (CRTP Pattern - like HostIO)
// ============================================================================

/// @brief Unified I/O interface for GPU memory operations
/// @note Inherits from IO<CudaIO> using CRTP pattern
/// @note GPU submit uses PRP1/PRP2 directly; poll wraps host implementation
class CudaIO : public IO<CudaIO> {
public:
    CudaIO() = default;
    ~CudaIO() = default;
    CudaIO(const CudaIO&) = delete;
    CudaIO& operator=(const CudaIO&) = delete;

    /// @brief Runtime dispatch for GPU submission
    virtual inline std::uint16_t submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, std::uint32_t nsid,
                                   std::uint64_t slba, std::uint32_t lba_size,
                                   DmaBuf* b, std::size_t bytes) override {
        // Extract PRPs from DmaBuf if provided, otherwise use zeros
        std::uint64_t prp1 = b ? b->prp1 : 0;
        std::uint64_t prp2 = b ? b->prp2 : 0;
        std::size_t actual_bytes = b ? b->bytes : bytes;
        // Convert doorbell pointer to enum for now (cuda_submit_runtime still accepts enum)
        DoorbellType db_enum = doorbell ? DOORBELL_DEFERRED : DOORBELL_MMIO;
        return ::cuda_submit_runtime(cmd, db_enum, iosq, nsid, slba, lba_size, actual_bytes, prp1, prp2);
    }

    /// @brief Runtime dispatch for polling (wraps host implementation)
    virtual inline NvmeStatus poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         std::uint16_t* out_cid,
                                         PollResult* out_poll_result = nullptr,
                                         std::uint32_t timeout_us = 0,
                                         Queue* iosq = nullptr) override {
        return ::host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us, iosq);
    }

    /// @brief Compile-time dispatch submit with DmaBuf
    template<CommandType cmd, DoorbellType doorbell>
    inline std::uint16_t submit(Queue* iosq, std::uint32_t nsid,
                                  std::uint64_t slba, std::uint32_t lba_size,
                                  DmaBuf* b, std::size_t bytes) {
        std::uint64_t prp1 = b ? b->prp1 : 0;
        std::uint64_t prp2 = b ? b->prp2 : 0;
        std::size_t actual_bytes = b ? b->bytes : bytes;
        return ::cuda_submit<cmd, doorbell>(iosq, nsid, slba, lba_size, actual_bytes, prp1, prp2);
    }

    /// @brief Compile-time dispatch submit with direct PRPs
    template<CommandType cmd, DoorbellType doorbell>
    inline std::uint16_t submit(Queue* iosq, std::uint32_t nsid,
                                  std::uint64_t slba, std::uint32_t lba_size,
                                  std::size_t bytes,
                                  std::uint64_t prp1, std::uint64_t prp2) {
        return ::cuda_submit<cmd, doorbell>(iosq, nsid, slba, lba_size, bytes, prp1, prp2);
    }

    /// @brief Compile-time dispatch poll (wraps host implementation)
    template<AsyncType async_type>
    inline NvmeStatus poll_completion(Queue* iocq, std::uint16_t* out_cid,
                                        PollResult* out_poll_result = nullptr,
                                        std::uint32_t timeout_us = 0) {
        return ::cuda_poll_completion<async_type>(iocq, out_cid, out_poll_result, timeout_us);
    }
};

// ============================================================================
// Compatibility Aliases
// ============================================================================

/// @note GPU memory uses host_poll_completion (completion is buffer-agnostic)
/// @note Provided by host_io_host_mem.h (included via mapping_host.h)
