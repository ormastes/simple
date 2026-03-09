/**
 * @file host_io_host_mem.cpp
 * @brief Host-side implementation for host_io_host_mem
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

#include <cstdint>
#include <cstddef>
#include <cstring>
#include <chrono>
#include <type_traits>
#include "mapper/mapper_host.h"
#include "host_io_host_mem.h"
#include "memory/host_memory_buffer.h"  // Provides host_pool_* implementation

extern "C" {

// Note: host_pool_* functions are implemented in host_memory_buffer.cpp
// No wrappers needed here - they are already available via host_memory_buffer.h

// ============================================================================
// Command Submission and Polling APIs
// ============================================================================

/// Unified NVMe command submission API (runtime dispatch)
/// Supports both READ and WRITE commands with configurable doorbell behavior
/// @param cmd Command type (CMD_READ or CMD_WRITE)
/// @param doorbell Doorbell handle (nullptr for immediate, or specific doorbell instance)
/// @param iosq I/O submission queue
/// @param nsid Namespace ID
/// @param slba Starting logical block address
/// @param lba_size Logical block size in bytes
/// @param b DMA buffer for transfer
/// @param bytes Number of bytes to transfer (must be multiple of lba_size)
/// @return CID (0-65534) on success, NVME_CID_QUEUE_FULL or NVME_CID_ERROR on failure
uint16_t host_submit_runtime(CommandType cmd, const DoorbellHandle* doorbell,
                                   Queue* iosq, uint32_t nsid,
                                   uint64_t slba, uint32_t lba_size,
                                   DmaBuf* b, size_t bytes)
{
  // Dispatch to specialized template based on runtime parameters
  // If doorbell is nullptr, use immediate doorbell
  // Otherwise check the type of the doorbell handle

  const DoorbellHandle* resolved = doorbell ? doorbell : &getImmediateDoorbellHandle();

  auto submit_with = [&](auto doorbell_tag) -> uint16_t {
    using DoorbellTag = std::decay_t<decltype(doorbell_tag)>;
    if (cmd == CMD_READ) {
      return host_submit<CMD_READ, DoorbellTag>(iosq, nsid, slba, lba_size, b, bytes);
    }
    if (cmd == CMD_WRITE) {
      return host_submit<CMD_WRITE, DoorbellTag>(iosq, nsid, slba, lba_size, b, bytes);
    }
    return NVME_CID_ERROR;
  };

  if (is_event_indexed_doorbell(*resolved)) {
    return submit_with(EventIndexedDoorbell{});
  }
  if (is_deferred_doorbell(*resolved)) {
    return submit_with(DeferredDoorbell{});
  }
  // Default to immediate MMIO doorbell semantics.
  return submit_with(ImmediateDoorbell{});
}

/// Unified completion polling API (runtime dispatch)
/// Supports both synchronous (blocking) and asynchronous (non-blocking) modes
/// @param async_type Polling mode (ASYNC_TYPE_SYNC or ASYNC_TYPE_ASYNC)
/// @param iocq I/O completion queue
/// @param[out] out_cid Pointer to store completed command ID (optional)
/// @param[out] out_poll_result Pointer to store PollResult (optional for sync, required for async)
/// @param timeout_us Timeout in microseconds (0 = infinite, only used in ASYNC_TYPE_SYNC)
/// @param[in] iosq Optional submission queue pointer to update SQ head from CQE
/// @return NvmeStatus (valid when POLL_READY, invalid otherwise in async mode)
NvmeStatus host_poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                         uint16_t* out_cid,
                                         PollResult* out_poll_result,
                                         uint32_t timeout_us,
                                         Queue* iosq)
{
  // Dispatch to specialized template based on runtime parameter
  // Compiler will optimize each template specialization independently

  switch (async_type) {
    case ASYNC_TYPE_SYNC:
      return host_poll_completion<ASYNC_TYPE_SYNC>(iocq, out_cid, out_poll_result, timeout_us, iosq);
    case ASYNC_TYPE_ASYNC:
      return host_poll_completion<ASYNC_TYPE_ASYNC>(iocq, out_cid, out_poll_result, timeout_us, iosq);
    default:
      if (out_poll_result) *out_poll_result = POLL_ERROR;
      return {0x7, 0xFF, true};
  }
}

} // extern "C"
