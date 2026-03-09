/**
 * @file cuda_io_host_mem_impl.h
 * @brief Template implementations for cuda_io_host_mem
 *
 * This file contains template function implementations that must be included
 * in the header to allow compile-time instantiation.
 *
 * Module 54 templates delegate to Module 53's host_submit/host_poll_completion
 * templates since CUDA host-pinned memory is compatible with VFIO DMA.
 */

#pragma once

// ============================================================================
// Template Specializations for Submit (All Combinations)
// ============================================================================

/// @note DOORBELL_MMIO template specializations removed
/// GPU cannot access MMIO registers - use DOORBELL_DEFERRED instead

/// Template implementation: READ + DOORBELL_DEFERRED
template<>
inline uint16_t cuda_host_submit<CMD_READ, DOORBELL_DEFERRED>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  // Forward to Module 53's template specialization
  return host_submit<CMD_READ, DOORBELL_DEFERRED>(iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: WRITE + DOORBELL_DEFERRED
template<>
inline uint16_t cuda_host_submit<CMD_WRITE, DOORBELL_DEFERRED>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  // Forward to Module 53's template specialization
  return host_submit<CMD_WRITE, DOORBELL_DEFERRED>(iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: READ + DOORBELL_DEFERRED_EVENTIDX
template<>
inline uint16_t cuda_host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  // Forward to Module 53's template specialization
  return host_submit<CMD_READ, DOORBELL_DEFERRED_EVENTIDX>(iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: WRITE + DOORBELL_DEFERRED_EVENTIDX
template<>
inline uint16_t cuda_host_submit<CMD_WRITE, DOORBELL_DEFERRED_EVENTIDX>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  // Forward to Module 53's template specialization
  return host_submit<CMD_WRITE, DOORBELL_DEFERRED_EVENTIDX>(iosq, nsid, slba, lba_size, b, bytes);
}

// ============================================================================
// Template Implementations for Completion Polling
// ============================================================================

/// Template implementation: ASYNC_TYPE_SYNC
template<>
inline NvmeStatus cuda_host_poll_completion<ASYNC_TYPE_SYNC>(
    Queue* iocq, uint16_t* out_cid,
    PollResult* out_poll_result, uint32_t timeout_us)
{
  // Forward to Module 53's template specialization
  return host_poll_completion<ASYNC_TYPE_SYNC>(iocq, out_cid, out_poll_result, timeout_us);
}

/// Template implementation: ASYNC_TYPE_ASYNC
template<>
inline NvmeStatus cuda_host_poll_completion<ASYNC_TYPE_ASYNC>(
    Queue* iocq, uint16_t* out_cid,
    PollResult* out_poll_result, uint32_t timeout_us)
{
  // Forward to Module 53's template specialization
  return host_poll_completion<ASYNC_TYPE_ASYNC>(iocq, out_cid, out_poll_result, timeout_us);
}
