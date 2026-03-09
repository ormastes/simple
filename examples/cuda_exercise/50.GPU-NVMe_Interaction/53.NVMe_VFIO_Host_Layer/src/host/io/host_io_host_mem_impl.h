/**
 * @file host_io_host_mem_impl.h
 * @brief Template implementations for host_io_host_mem
 *
 * This file contains template function implementations that must be included
 * in the header to allow compile-time instantiation.
 *
 * Uses shared implementations from:
 * - memory_buffer_impl.h: PRP building
 * - io_impl.h: Command building, CQE parsing
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <chrono>
#include <utility>
#include "io/io_impl.h"

// Import shared implementations into local namespace for convenience
using nvme_io_impl::build_command;
using nvme_io_impl::copy_64B;
using nvme_io_impl::cqe_phase;
using nvme_io_impl::cqe_sct;
using nvme_io_impl::cqe_sc;

// ============================================================================
// Backward Compatibility: Legacy Enum-Based API Support
// ============================================================================

// Add overloaded template function that accepts DoorbellType enum
// and forwards to the new type-based templates
template<CommandType cmd, DoorbellType doorbell>
inline uint16_t host_submit(Queue* iosq, uint32_t nsid,
                                  uint64_t slba, uint32_t lba_size,
                                  DmaBuf* b, size_t bytes) {
    if constexpr (doorbell == DOORBELL_MMIO) {
        return host_submit<cmd, ImmediateDoorbell>(iosq, nsid, slba, lba_size, b, bytes);
    } else if constexpr (doorbell == DOORBELL_DEFERRED) {
        return host_submit<cmd, DeferredDoorbell>(iosq, nsid, slba, lba_size, b, bytes);
    } else if constexpr (doorbell == DOORBELL_DEFERRED_EVENTIDX) {
        return host_submit<cmd, EventIndexedDoorbell>(iosq, nsid, slba, lba_size, b, bytes);
    } else {
        // Should never happen with enum values
        return NVME_CID_ERROR;
    }
}

// Wrapper for DmaBuf-based PRP building
inline void build_prps(const DmaBuf& b, size_t bytes,
                       uint64_t& prp1, uint64_t& prp2)
{
  nvme_buffer_impl::build_prps(b.iova, b.prplist_iova, bytes, prp1, prp2);
}

namespace detail {

struct ImmediateDoorbellPolicy {
    static inline void on_submit(Queue* iosq) { *iosq->db = iosq->tail; }
};

struct DeferredDoorbellPolicy {
    static inline void on_submit(Queue*) {}
};

inline bool has_valid_submit_args(const Queue* iosq, const DmaBuf* b,
                                  uint32_t lba_size, size_t bytes) {
    if (!iosq || !b || !iosq->db || !iosq->vaddr) {
        if (!iosq) fprintf(stderr, "SUBMIT_DEBUG: iosq is NULL\n");
        if (iosq && !iosq->db) fprintf(stderr, "SUBMIT_DEBUG: iosq->db is NULL\n");
        if (iosq && !iosq->vaddr) fprintf(stderr, "SUBMIT_DEBUG: iosq->vaddr is NULL\n");
        if (!b) fprintf(stderr, "SUBMIT_DEBUG: DmaBuf is NULL\n");
        return false;
    }
    if (!lba_size || !bytes || bytes > b->bytes || (lba_size && (bytes % lba_size))) {
        if (!lba_size) fprintf(stderr, "SUBMIT_DEBUG: lba_size is 0\n");
        if (!bytes) fprintf(stderr, "SUBMIT_DEBUG: bytes is 0\n");
        if (bytes > b->bytes) fprintf(stderr, "SUBMIT_DEBUG: bytes(%zu) > b->bytes(%zu)\n", bytes, b->bytes);
        if (lba_size && (bytes % lba_size)) fprintf(stderr, "SUBMIT_DEBUG: bytes(%zu) not multiple of lba_size(%u)\n", bytes, lba_size);
        return false;
    }
    return true;
}

inline std::pair<uint64_t, uint64_t> compute_runtime_prps(const DmaBuf* b, size_t bytes) {
    if (b->prp1 != 0) {
        return {b->prp1, b->prp2};
    }
    const size_t pages = (bytes + 4095) / 4096;
    if (pages == 1) {
        return {b->iova, 0ULL};
    }
    if (pages == 2) {
        return {b->iova, static_cast<uint64_t>(b->iova + 4096)};
    }
    return {b->iova, static_cast<uint64_t>(b->prplist_iova)};
}

template<CommandType cmd>
inline NvmeCmd compose_command(Queue* iosq, uint32_t nsid, uint64_t slba,
                               uint32_t lba_size, DmaBuf* b, size_t bytes, uint16_t cid) {
    NvmeCmd cmd_out{};
    NvmeCmd* pool = nullptr;
    if constexpr (cmd == CMD_READ) {
        pool = iosq->read_cmd_pool;
    } else {
        pool = iosq->write_cmd_pool;
    }

    if (pool) {
        cmd_out = pool[cid];
        auto [prp1, prp2] = compute_runtime_prps(b, bytes);
        cmd_out.prp1 = prp1;
        cmd_out.prp2 = prp2;
        cmd_out.cdw10 = static_cast<uint32_t>(slba & 0xFFFFFFFFu);
        cmd_out.cdw11 = static_cast<uint32_t>(slba >> 32);
    } else {
        auto [prp1, prp2] = compute_runtime_prps(b, bytes);
        const uint16_t nlb0 = static_cast<uint16_t>((bytes / lba_size) - 1);
        build_command(cmd, nsid, slba, nlb0, prp1, prp2, cid, cmd_out);
    }
    return cmd_out;
}

template<CommandType cmd, typename DoorbellPolicy>
uint16_t submit_impl(Queue* iosq, uint32_t nsid, uint64_t slba,
                     uint32_t lba_size, DmaBuf* b, size_t bytes) {
    if (!has_valid_submit_args(iosq, b, lba_size, bytes)) {
        return NVME_CID_ERROR;
    }

    const uint16_t next_tail = static_cast<uint16_t>((iosq->tail + 1) % iosq->entries);
    if (next_tail == iosq->head) {
        return NVME_CID_QUEUE_FULL;
    }

#ifndef NDEBUG
    if (b->item_size.is_valid() && bytes != b->item_size.total_size) {
        std::fprintf(stderr, "WARNING: host_submit - Buffer size mismatch: requested %zu, ItemSize %u\n",
                     bytes, b->item_size.total_size);
    }
#endif

    const uint16_t cid = iosq->tail;
    NvmeCmd nvme_cmd = compose_command<cmd>(iosq, nsid, slba, lba_size, b, bytes, cid);

    b->cid_hint = cid;
    void* slot = static_cast<uint8_t*>(iosq->vaddr) + static_cast<size_t>(iosq->tail) * iosq->entry_size;
    copy_64B(slot, &nvme_cmd);
    iosq->tail = next_tail;
    DoorbellPolicy::on_submit(iosq);

    return nvme_cmd.cid;
}

}  // namespace detail

// ============================================================================
// Template Declarations (Primary templates, specialized below)
// ============================================================================

/// Primary template for host submit (specialized for each Command/Doorbell combination)
template<CommandType cmd, typename DoorbellT>
inline uint16_t host_submit(Queue* iosq, uint32_t nsid,
                                 uint64_t slba, uint32_t lba_size,
                                 DmaBuf* b, size_t bytes);

/// Primary template for host poll completion (specialized for sync/async)
template<AsyncType async_type>
inline NvmeStatus host_poll_completion(Queue* iocq, uint16_t* out_cid,
                                      PollResult* out_poll_result,
                                      uint32_t timeout_us,
                                      Queue* iosq);

// ============================================================================
// Template Specializations for Submit (All Combinations)
// ============================================================================

/// Template implementation: READ + ImmediateDoorbell
template<>
inline uint16_t host_submit<CMD_READ, ImmediateDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_READ, detail::ImmediateDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: WRITE + ImmediateDoorbell
template<>
inline uint16_t host_submit<CMD_WRITE, ImmediateDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_WRITE, detail::ImmediateDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: READ + DeferredDoorbell
template<>
inline uint16_t host_submit<CMD_READ, DeferredDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_READ, detail::DeferredDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: WRITE + DeferredDoorbell
template<>
inline uint16_t host_submit<CMD_WRITE, DeferredDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_WRITE, detail::DeferredDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: READ + EventIndexedDoorbell
template<>
inline uint16_t host_submit<CMD_READ, EventIndexedDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_READ, detail::DeferredDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

/// Template implementation: WRITE + EventIndexedDoorbell
template<>
inline uint16_t host_submit<CMD_WRITE, EventIndexedDoorbell>(
    Queue* iosq, uint32_t nsid, uint64_t slba,
    uint32_t lba_size, DmaBuf* b, size_t bytes)
{
  return detail::submit_impl<CMD_WRITE, detail::DeferredDoorbellPolicy>(
      iosq, nsid, slba, lba_size, b, bytes);
}

// ============================================================================
// Template Implementations for Completion Polling
// ============================================================================

/// Template implementation: ASYNC_TYPE_SYNC
template<>
inline NvmeStatus host_poll_completion<ASYNC_TYPE_SYNC>(
    Queue* iocq, uint16_t* out_cid,
    PollResult* out_poll_result, uint32_t timeout_us,
    Queue* iosq)
{
  if (!iocq || !iocq->db || !iocq->vaddr) {
    if (out_poll_result) *out_poll_result = POLL_ERROR;
    return {0x7, 0xFF, true};
  }

  // Infinite wait (timeout_us == 0)
  if (timeout_us == 0) {
    for (;;) {
      // Inline poll_try_once logic
      NvmeCqe* cqe = (NvmeCqe*)((uint8_t*)iocq->vaddr +
                                (size_t)iocq->head * iocq->entry_size);
      if (cqe_phase(*cqe) == iocq->phase) {
        uint8_t sct = cqe_sct(*cqe);
        uint8_t sc = cqe_sc(*cqe);
        uint16_t cmd_id = cqe->cid;
        uint16_t sqhd = cqe->sqhd;  // Extract SQ head from CQE
        iocq->head = (uint16_t)((iocq->head + 1) % iocq->entries);
        if (iocq->head == 0) {
          iocq->phase ^= 1u;
        }
        *iocq->db = iocq->head;
        // Update submission queue head if provided
        if (iosq) {
          iosq->head = sqhd;
        }
        if (out_cid) *out_cid = cmd_id;
        if (out_poll_result) *out_poll_result = POLL_READY;
        return {sct, sc, false};
      }
      asm volatile("pause");
    }
  }

  // Timed wait (timeout_us > 0)
  auto start_time = std::chrono::steady_clock::now();
  const auto timeout_duration = std::chrono::microseconds(timeout_us);

  while (true) {
    // Inline poll_try_once logic
    NvmeCqe* cqe = (NvmeCqe*)((uint8_t*)iocq->vaddr +
                              (size_t)iocq->head * iocq->entry_size);
    if (cqe_phase(*cqe) == iocq->phase) {
      uint8_t sct = cqe_sct(*cqe);
      uint8_t sc = cqe_sc(*cqe);
      uint16_t cmd_id = cqe->cid;
      uint16_t sqhd = cqe->sqhd;  // Extract SQ head from CQE
      iocq->head = (uint16_t)((iocq->head + 1) % iocq->entries);
      if (iocq->head == 0) {
        iocq->phase ^= 1u;
      }
      *iocq->db = iocq->head;
      // Update submission queue head if provided
      if (iosq) {
        iosq->head = sqhd;
      }
      if (out_cid) *out_cid = cmd_id;
      if (out_poll_result) *out_poll_result = POLL_READY;
      return {sct, sc, false};
    }

    auto elapsed = std::chrono::steady_clock::now() - start_time;
    if (elapsed >= timeout_duration) {
      if (out_poll_result) *out_poll_result = POLL_TIMEOUT;
      return {0x7, 0xFE, true};
    }

    asm volatile("pause");
  }
}

/// Template implementation: ASYNC_TYPE_ASYNC
template<>
inline NvmeStatus host_poll_completion<ASYNC_TYPE_ASYNC>(
    Queue* iocq, uint16_t* out_cid,
    PollResult* out_poll_result, uint32_t timeout_us,
    Queue* iosq)
{
  (void)timeout_us;  // Unused in async mode

  if (!iocq || !iocq->db || !iocq->vaddr || !out_poll_result) {
    if (out_poll_result) *out_poll_result = POLL_ERROR;
    return {0x7, 0xFF, true};
  }

  // Inline poll_try_once logic
  NvmeCqe* cqe = (NvmeCqe*)((uint8_t*)iocq->vaddr +
                            (size_t)iocq->head * iocq->entry_size);
  if (cqe_phase(*cqe) == iocq->phase) {
    uint8_t sct = cqe_sct(*cqe);
    uint8_t sc = cqe_sc(*cqe);
    uint16_t cmd_id = cqe->cid;
    uint16_t sqhd = cqe->sqhd;  // Extract SQ head from CQE
    iocq->head = (uint16_t)((iocq->head + 1) % iocq->entries);
    if (iocq->head == 0) {
      iocq->phase ^= 1u;
    }
    *iocq->db = iocq->head;
    // Update submission queue head if provided
    if (iosq) {
      iosq->head = sqhd;
    }
    if (out_cid) *out_cid = cmd_id;
    *out_poll_result = POLL_READY;
    return {sct, sc, false};
  }
  *out_poll_result = POLL_NOT_READY;
  return {0, 0, false};
}
