/**
 * @file memory_types.h
 * @brief Common memory buffer enums and structures shared across modules.
 *
 * This header extracts the lightweight type definitions that used to live in
 * memory_buffer.h so individual components (pool, factory, mapping) can include
 * only what they need without dragging in additional implementation files.
 */

#pragma once

#include <cstddef>
#include <cstdint>

#include "cuda_utils.h"

// ============================================================================
// Buffer Type Enumeration
// ============================================================================

/// Memory location: HOST (CPU) or DEVICE (GPU)
enum class MemoryLocation : uint8_t {
    HOST   = 0,
    DEVICE = 1
};

/// Memory pinning: NOT_PINNED (pageable) or PINNED (non-pageable for DMA)
enum class Pinned : uint8_t {
    NOT_PINNED = 0,
    PINNED     = 1
};

/// Memory type: HOST (M53), PINNED_HOST (M54), PINNED_DEVICE (M55-56)
enum class MemoryType : uint8_t {
    HOST          = 0,  ///< Pageable host (M53)
    PINNED_HOST   = 1,  ///< Pinned host (M54)
    PINNED_DEVICE = 2   ///< GPU device (M55-56)
};

/// Buffer usage: NONE_CONSECUTIVE (pool) or CONSECUTIVE (standalone)
enum class Consecutive : uint8_t {
    NONE_CONSECUTIVE = 0,
    CONSECUTIVE      = 1
};

/// IOVA segment for GPU scatter-gather
struct IovaSeg {
    uint64_t iova{0};
    size_t   bytes{0};
};

/// Transfer size aligned to LBA boundaries
struct ItemSize {
    uint32_t total_size{0};  ///< Total bytes
    uint32_t lba_size{0};    ///< LBA bytes
    uint32_t lba_count{0};   ///< LBA count

    /// Check valid (lba_size > 0 && total_size == lba_size * lba_count)
    __device__ __host__ inline bool is_valid() const {
        return lba_size > 0 && lba_count > 0 && total_size == (lba_size * lba_count);
    }

    /// NLB for NVMe commands (0-based: lba_count - 1)
    __device__ __host__ inline uint16_t nlb() const {
        return static_cast<uint16_t>(lba_count - 1);
    }
};

// ============================================================================
// DMA Buffer Structures
// ============================================================================

/// Unified DMA buffer (host and GPU)
struct DmaBuf {
    void*          addr{nullptr};
    size_t    bytes{0};
    uint64_t  iova{0};              ///< Base IOVA (contiguous for host, first seg for GPU)
    void*          prplist_host{nullptr};
    uint64_t  prplist_iova{0};
    size_t    prplist_bytes{0};
    uint16_t  cid_hint{0};
    bool using_p2p{false};  // True when PRP/I/O comes from GPU P2P mapping
    void*          device_alias{nullptr};  ///< Optional device shadow (host pools)
    MemoryType     mem_type{MemoryType::HOST};
    Consecutive    consecutive{Consecutive::NONE_CONSECUTIVE};
    ItemSize       item_size{};          ///< Pre-computed for pool
    uint64_t  prp1{0};              ///< Pre-computed PRP1
    uint64_t  prp2{0};              ///< Pre-computed PRP2
    IovaSeg*       segs{nullptr};        ///< GPU scatter-gather
    size_t    nseg{0};

    // Host VFIO helpers
    __device__ __host__ inline uint64_t iova_aligned() const { return (iova + 4095) & ~4095UL; }
    __device__ __host__ inline size_t map_size() const {
        if (bytes == 0) return 0;
        return static_cast<size_t>(((iova + bytes + 4095) & ~4095UL) - iova_aligned());
    }
    __device__ __host__ inline uint64_t prplist_iova_aligned() const { return (prplist_iova + 4095) & ~4095UL; }
    __device__ __host__ inline size_t prplist_map_size() const {
        if (prplist_bytes == 0) return 0;
        return static_cast<size_t>(((prplist_iova + prplist_bytes + 4095) & ~4095UL) - prplist_iova_aligned());
    }

    // GPU helpers
    __device__ __host__ inline size_t prplist_capacity() const { return prplist_bytes / sizeof(uint64_t); }

    // Type checks
    __device__ __host__ inline bool is_host() const {
        return mem_type == MemoryType::HOST || mem_type == MemoryType::PINNED_HOST;
    }
    __device__ __host__ inline bool is_gpu() const { return mem_type == MemoryType::PINNED_DEVICE; }
    __device__ __host__ inline bool is_pinned() const {
        return mem_type == MemoryType::PINNED_HOST || mem_type == MemoryType::PINNED_DEVICE;
    }
    __device__ __host__ inline bool is_pooled() const { return consecutive == Consecutive::NONE_CONSECUTIVE; }
    __device__ __host__ inline bool is_consecutive() const { return consecutive == Consecutive::CONSECUTIVE; }
    __device__ __host__ inline bool has_contiguous_iova() const {
        return mem_type == MemoryType::HOST || mem_type == MemoryType::PINNED_HOST;
    }
    __device__ __host__ inline bool may_have_scattered_iova() const { return mem_type == MemoryType::PINNED_DEVICE; }
};

// Helper factories
inline DmaBuf* create_host_dmabuf() { auto* b = new DmaBuf(); b->mem_type = MemoryType::HOST; return b; }
inline DmaBuf* create_cuda_host_dmabuf() { auto* b = new DmaBuf(); b->mem_type = MemoryType::PINNED_HOST; return b; }
inline DmaBuf* create_gpu_dmabuf() { auto* b = new DmaBuf(); b->mem_type = MemoryType::PINNED_DEVICE; return b; }

/// Standalone buffer (create/destroy pattern, lightweight vs DmaBuf)
struct Buffer {
    void*         addr{nullptr};
    size_t   bytes{0};
    uint64_t iova{0};
    MemoryType    mem_type{MemoryType::HOST};
    Consecutive   consecutive{Consecutive::NONE_CONSECUTIVE};
    IovaSeg*      segs{nullptr};         ///< GPU scatter-gather
    size_t   nseg{0};

    __device__ __host__ inline bool has_contiguous_iova() const {
        return (mem_type == MemoryType::HOST || mem_type == MemoryType::PINNED_HOST) &&
               consecutive == Consecutive::CONSECUTIVE;
    }
    __device__ __host__ inline bool is_gpu() const {
        return mem_type == MemoryType::PINNED_DEVICE && consecutive == Consecutive::CONSECUTIVE;
    }
};
