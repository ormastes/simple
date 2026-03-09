/**
 * @file nvme_queue.h
 * @brief Unified NVMe queue structures and CRTP-based queue operations for host/GPU
 */

#pragma once

#include <cstdint>
#include <cstddef>
#include "nvme_types.h"      // For NvmeCmd, NvmeCqe, NvmeStatus
#include "memory/memory_types.h"   // For ItemSize
#include "io/io_impl.h"         // For unified command building and CQE parsing (no Queue dependency now)
#include "doorbell/nvme_doorbell.h"   // For DoorbellStrategy, MmioDoorbell, ShadowDoorbell
#include "cuda_utils.h"       // For CUDA compatibility macros

// ============================================================================
// Unified NVMe Queue Structure
// ============================================================================
//
// Note: DoorbellMode enum is defined in doorbell/nvme_doorbell.h

/// NVMe queue descriptor (POD for host-GPU transfer, used in M53-56)
struct NvmeQueueStruct {
    NvmeCmd*   sq_base;              ///< SQ virtual address
    NvmeCqe*   cq_base;              ///< CQ virtual address
    void* sq_addr;                   ///< SQ IOVA (VFIO mapping)
    void* cq_addr;                   ///< CQ IOVA (VFIO mapping)
    uint16_t sq_depth;          ///< SQ depth (power of 2)
    uint16_t cq_depth;          ///< CQ depth (power of 2)
    uint16_t qid;               ///< Queue ID
    uint32_t nsid;              ///< Namespace ID
    uint32_t page_size;         ///< NVMe page size (for PRP)
    uint8_t  sq_phase;          ///< SQ phase bit
    uint8_t  cq_phase;          ///< CQ phase bit (toggles on wrap)
    DoorbellMode  doorbell_mode;     ///< Doorbell mode
    uint8_t  padding;           ///< Alignment padding
    unsigned int  sq_tail;           ///< SQ tail (visible to daemon/controller)
    unsigned int  sq_internal_tail;  ///< SQ internal tail (for slot allocation, GPU-only)
    unsigned int  sq_head;           ///< SQ head (from CQE sqhd field, indicates consumed commands)
    unsigned int  cq_head;           ///< CQ head (atomic for GPU)
    NvmeCmd*   read_cmd_pool;        ///< Pre-built READ commands
    NvmeCmd*   write_cmd_pool;       ///< Pre-built WRITE commands
    ItemSize   item_size;            ///< ItemSize for buffer pool

    // Optional shadow doorbell pointers (host-mapped, GPU-visible)
    volatile uint32_t* shadow_doorbell_sq{nullptr};  ///< Shadow SQ doorbell base
    volatile uint32_t* shadow_doorbell_cq{nullptr};  ///< Shadow CQ doorbell base

    // For Mode 5 daemon: original VFIO queue pointers (host only, not GPU-accessible)
    NvmeCmd*   vfio_sq_base{nullptr};   ///< Original VFIO SQ (daemon copies shadow -> VFIO)
    NvmeCqe*   vfio_cq_base{nullptr};   ///< Original VFIO CQ (daemon copies VFIO -> shadow)
    volatile uint32_t* mmio_sq_doorbell{nullptr};  ///< MMIO SQ doorbell (daemon rings this)
    volatile uint32_t* mmio_cq_doorbell{nullptr};  ///< MMIO CQ doorbell (daemon rings this)
};

// ============================================================================
// NVMe Queue Class
// ============================================================================

/**
 * @brief NVMe queue operations with compile-time doorbell dispatch
 * @tparam DoorbellT Doorbell strategy (MmioDoorbell or ShadowDoorbell)
 *
 * Derived classes: HostNvmeQueue (sequential), GpuNvmeQueue (atomic).
 */
template<typename DoorbellT>
class NvmeQueue {
protected:
    // Queue Memory
    NvmeCmd* sq_base_;  ///< Submission Queue base address
    NvmeCqe* cq_base_;  ///< Completion Queue base address

    // Queue State
    uint16_t sq_tail_;   ///< SQ tail (next slot to write)
    uint16_t sq_depth_;  ///< SQ depth (total entries)
    uint16_t cq_head_;   ///< CQ head (next slot to read)
    uint16_t cq_depth_;  ///< CQ depth (total entries)
    uint8_t  cq_phase_;  ///< CQ phase bit (toggles on wrap)

    // Doorbell Strategy
    DoorbellT doorbell_;  ///< Doorbell strategy instance (MMIO or Shadow)

    // Metadata
    uint32_t nsid_;      ///< Namespace ID
    uint32_t lba_size_;  ///< Logical Block size in bytes

public:
    /// Construct queue with memory, depth, doorbell strategy, and namespace params
    __device__ __host__
    NvmeQueue(NvmeCmd* sq, NvmeCqe* cq,
              uint16_t sq_depth, uint16_t cq_depth,
              DoorbellT&& doorbell,
              uint32_t nsid, uint32_t lba_size)
        : sq_base_(sq), cq_base_(cq),
          sq_tail_(0), sq_depth_(sq_depth),
          cq_head_(0), cq_depth_(cq_depth), cq_phase_(1),
          doorbell_(std::move(doorbell)),
          nsid_(nsid), lba_size_(lba_size) {}

    // ========================================================================
    // Doorbell Operations (Delegate to Strategy)
    // ========================================================================

    /// Ring SQ doorbell (compile-time dispatch to DoorbellT)
    __device__ __host__ inline void ring_sq_doorbell() {
        doorbell_.ring_sq_doorbell(sq_tail_);
    }

    /// Ring CQ doorbell
    __device__ __host__ inline void ring_cq_doorbell() {
        doorbell_.ring_cq_doorbell(cq_head_);
    }

    // ========================================================================
    // Queue State Accessors
    // ========================================================================

    __device__ __host__ inline uint16_t sq_tail() const { return sq_tail_; }
    __device__ __host__ inline uint16_t sq_depth() const { return sq_depth_; }
    __device__ __host__ inline uint16_t cq_head() const { return cq_head_; }
    __device__ __host__ inline uint16_t cq_depth() const { return cq_depth_; }
    __device__ __host__ inline uint8_t cq_phase() const { return cq_phase_; }
    __device__ __host__ inline uint32_t nsid() const { return nsid_; }
    __device__ __host__ inline uint32_t lba_size() const { return lba_size_; }
    __device__ __host__ inline NvmeCmd* sq_base() const { return sq_base_; }
    __device__ __host__ inline NvmeCqe* cq_base() const { return cq_base_; }
    __device__ __host__ inline DoorbellT& doorbell() { return doorbell_; }
    __device__ __host__ inline const DoorbellT& doorbell() const { return doorbell_; }

    // ========================================================================
    // Helper Functions for Derived Classes
    // ========================================================================

    /// Advance CQ head and toggle phase on wrap
    __device__ __host__ inline void advance_cq_head() {
        cq_head_ = (cq_head_ + 1) % cq_depth_;
        if (cq_head_ == 0) cq_phase_ ^= 1;
    }

    /// Check if CQE phase matches expected (new completion available)
    __device__ __host__ inline bool cqe_is_new(const NvmeCqe& cqe) const {
        using nvme_io_impl::cqe_phase;
        return cqe_phase(cqe) == cq_phase_;
    }

    /// Parse CQE into NvmeStatus
    __device__ __host__ inline void parse_cqe(const NvmeCqe& cqe, NvmeStatus* status) const {
        using nvme_io_impl::cqe_sct;
        using nvme_io_impl::cqe_sc;
        using nvme_io_impl::cqe_dnr;
        status->sct = cqe_sct(cqe);
        status->sc = cqe_sc(cqe);
        status->dnr = cqe_dnr(cqe);
    }

protected:
    ~NvmeQueue() = default;
};

/// Type trait for NVMe queue verification
template<typename T>
struct is_nvme_queue {
    static constexpr bool value = false;
};

template<typename T>
inline constexpr bool is_nvme_queue_v = is_nvme_queue<T>::value;
