/**
 * @file host_io_host_mem.h
 * @brief Host I/O submission and polling APIs
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include "memory/memory_pool.h"
#include "mapper/mapper_host.h"       // For NvmeQueue and nvme_setup_host_queue
#include "io/io.h"
#include "memory/host_memory_buffer.h"  // Provides host_pool_* implementation
#include "doorbell/nvme_doorbell.h"     // For doorbell types

// Buffer pool APIs in host_memory_buffer.h; I/O submission APIs here

extern "C" {

// ============================================================================
// Unified Command Submission API (Runtime)
// ============================================================================

/// Runtime submit (cmd: READ/WRITE, doorbell: nullptr=immediate, else deferred)
/// Returns: CID (0-65534), NVME_CID_QUEUE_FULL (0xFFFE), or NVME_CID_ERROR (0xFFFF)
uint16_t host_submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, uint32_t nsid,
                                   uint64_t slba, uint32_t lba_size,
                                   DmaBuf* b, size_t bytes);

// ============================================================================
// Completion Polling API (Runtime)
// ============================================================================

/// Runtime poll (async_type: SYNC=blocking, ASYNC=non-blocking)
/// SYNC: returns valid NvmeStatus when ready, POLL_TIMEOUT if timeout
/// ASYNC: check out_poll_result for POLL_READY/POLL_NOT_READY, NvmeStatus valid only if POLL_READY
NvmeStatus host_poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         uint16_t* out_cid,
                                         PollResult* out_poll_result = nullptr,
                                         uint32_t timeout_us = 0,
                                         Queue* iosq = nullptr);

} // extern "C"

// ============================================================================
// Template-Based APIs (Compile-Time Dispatch)
// ============================================================================

/// Template submit (compile-time cmd and DoorbellT, eliminates runtime branches)
template<CommandType cmd, typename DoorbellT>
uint16_t host_submit(Queue* iosq, uint32_t nsid,
                          uint64_t slba, uint32_t lba_size,
                          DmaBuf* b, size_t bytes);

/// Template poll (compile-time async_type, eliminates runtime branches)
template<AsyncType async_type>
NvmeStatus host_poll_completion(Queue* iocq, uint16_t* out_cid,
                                 PollResult* out_poll_result = nullptr,
                                 uint32_t timeout_us = 0,
                                 Queue* iosq = nullptr);

class  HostIO : public IO<HostIO> {
public:
    HostIO() = default;
    ~HostIO() = default;
    HostIO(const HostIO&) = delete;
    HostIO& operator=(const HostIO&) = delete;

    virtual inline uint16_t submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, uint32_t nsid,
                                   uint64_t slba, uint32_t lba_size,
                                   DmaBuf* b, size_t bytes) override {
        return ::host_submit_runtime(cmd, doorbell, iosq, nsid, slba, lba_size, b, bytes);
    }
    virtual inline NvmeStatus poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         uint16_t* out_cid,
                                         PollResult* out_poll_result = nullptr,
                                         uint32_t timeout_us = 0,
                                         Queue* iosq = nullptr) override {
        return ::host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us, iosq);
    }
    template<CommandType cmd, typename DoorbellT>
    inline uint16_t submit(Queue* iosq, uint32_t nsid,
                                  uint64_t slba, uint32_t lba_size,
                                  DmaBuf* b, size_t bytes) {
        return ::host_submit<cmd, DoorbellT>(iosq, nsid, slba, lba_size, b, bytes);
    }
    template<AsyncType async_type>
    inline NvmeStatus poll_completion(Queue* iocq, uint16_t* out_cid,
                                        PollResult* out_poll_result = nullptr,
                                        uint32_t timeout_us = 0) {
        return ::host_poll_completion<async_type>(iocq, out_cid, out_poll_result, timeout_us);
    }
};

// Include template implementations
#include "host_io_host_mem_impl.h"
