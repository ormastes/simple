/**
 * @file host_memory_buffer.h
 * @brief Host memory buffer pool management for NVMe DMA operations
 *
 * Provides buffer pool allocation, VFIO DMA mapping, and consecutive buffer
 * creation for host pageable memory (Module 53).
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cassert>
#include "memory/memory_pool.h"      // For DmaBuf, Pool, Buffer
#include "mapper/mapper.h"
#include "mapper/mapper_host_impl.h" // For NvmeQueue
#include "forward_decls.h"

class MapperInterface;

extern "C" {

// ============================================================================
// Host Memory Buffer Pool API (Module 53)
// ============================================================================

/// Create pre-allocated pool of host pageable buffers with VFIO DMA mapping
///
/// Allocates `count` buffers based on ItemSize, maps them to IOVA space via
/// VFIO for DMA operations, and returns a pool handle for buffer management.
/// Pre-computes PRP1/PRP2 for each buffer during pool creation.
///
/// @param d NVMe device handle (for VFIO DMA mapping and ItemSize)
/// @param count Number of buffers in pool
/// @param mapping Optional mapping interface (uses global mapping if nullptr)
/// @return Pool handle, or nullptr on failure
///
/// Usage:
///   HostPool* pool = host_pool_create(dev, 16);  // ItemSize from dev
///   DmaBuf* buf = host_pool_acquire(pool);
///   // Use buf for NVMe I/O (PRP1/PRP2 pre-computed)...
///   host_pool_release(pool, buf);
///   host_pool_destroy(pool);
///
HostPool* host_pool_create(NvmeDevice* d, uint16_t count, MapperInterface* mapping = nullptr);

/// Acquire buffer from pool (non-blocking)
///
/// @param p Pool handle
/// @return DmaBuf with host pageable memory, or nullptr if pool full
DmaBuf* host_pool_acquire(HostPool* p);

/// Release buffer back to pool
///
/// @param p Pool handle
/// @param b Buffer to release (can be nullptr)
void host_pool_release(HostPool* p, DmaBuf* b);

/// Destroy pool and free all buffers
///
/// Unmaps all VFIO DMA mappings and frees host memory.
///
/// @param p Pool handle
/// @param mapping Optional mapping interface (uses global mapping if nullptr)
void host_pool_destroy(HostPool* p, MapperInterface* mapping = nullptr);

// ============================================================================
// Host Consecutive Buffer API (Module 53.3)
// ============================================================================

/// Create host pageable consecutive buffer with VFIO DMA mapping
///
/// Allocates a single large buffer with consecutive IOVA addresses, suitable
/// for large sequential I/O operations.
///
/// @param buffer_size Size of buffer in bytes (will be page-aligned)
/// @param mapping Optional mapping interface (uses global mapping if nullptr)
/// @return Buffer descriptor, or nullptr on failure
Buffer* host_create_consecutive_buffer(size_t buffer_size, MapperInterface* mapping = nullptr);

/// Destroy host consecutive buffer
///
/// Unmaps VFIO DMA mapping and frees host memory.
///
/// @param b Buffer to destroy
/// @param mapping Optional mapping interface (uses global mapping if nullptr)
void host_buffer_destroy(Buffer* b, MapperInterface* mapping = nullptr);

// ============================================================================
// Host Memory Mapping API (Module 53)
// ============================================================================
// Note: Memory mapping functions (host_map_iova/host_unmap_iova) are now
// available through:
//   1. The Mapping interface in mapping/mapping.h (recommended)
//   2. Direct functions in mapping/mapping_host.h (for backward compatibility)
// Pool implementations should use the Mapping interface for IOVA operations

// ============================================================================
// Host Memory Pool Implementation
// ============================================================================
//
// Note: HostPool is now defined in memory_buffer.h as Pool<std::vector<DmaBuf>>
// IOVA mapping is handled during pool creation via fill_pool_buffers()
// No separate struct needed here

} // extern "C"

// Include implementation
#include "host_memory_buffer_impl.h"
