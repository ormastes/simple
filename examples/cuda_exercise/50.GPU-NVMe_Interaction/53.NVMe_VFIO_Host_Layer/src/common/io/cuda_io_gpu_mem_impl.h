/**
 * @file cuda_io_gpu_mem_impl.h
 * @brief Internal/private implementation details for cuda_io_gpu_mem
 *
 * This header contains internal helper functions that should NOT be used
 * directly by external code. These are implementation details.
 */

#pragma once
#include <cstdint>
#include <cstddef>

// Forward declaration
struct IovaSeg;

// ============================================================================
// Internal PRP Building Functions (Private - Do Not Use Directly)
// ============================================================================

/// Build NVMe PRP (Physical Region Page) list for GPU memory segments
/// This is an internal function - use cuda_gpu_pool_* APIs instead
///
/// @param segs Array of IOVA segments (must be page-aligned)
/// @param nsegs Number of segments
/// @param[out] out_prp1 First page IOVA address
/// @param[out] out_prp2 Second page IOVA or PRP list pointer
/// @param[out] prp_list Array to store PRP list entries (pages 2..N)
/// @param prp_list_capacity_entries Capacity of prp_list array
/// @return Total transfer size in bytes, or 0 on error
///
/// @internal
std::size_t build_prps_for_gpu(const IovaSeg* segs, std::size_t nsegs,
                               std::uint64_t* out_prp1,
                               std::uint64_t* out_prp2,
                               std::uint64_t* prp_list,
                               std::size_t    prp_list_capacity_entries);

/// Enhanced version that accepts IOVA of the PRP list for proper DMA mapping
/// This is an internal function - use cuda_gpu_pool_* APIs instead
///
/// @param prp_list_iova IOVA address of prp_list (for real hardware), 0 for testing
/// @return Total transfer size in bytes, or 0 on error
///
/// @internal
std::size_t build_prps_for_gpu_ex(const IovaSeg* segs, std::size_t nsegs,
                                  std::uint64_t* out_prp1,
                                  std::uint64_t* out_prp2,
                                  std::uint64_t* prp_list,
                                  std::size_t    prp_list_capacity_entries,
                                  std::uint64_t  prp_list_iova);

// ============================================================================
// Internal CUDA Host Memory Functions (Private - Do Not Use Directly)
// ============================================================================

/// Allocate CUDA host-pinned memory (internal helper)
/// @internal Use cuda_gpu_pool_create() or higher-level APIs instead
int cuda_host_alloc(void** out_host, std::size_t bytes);

/// Free CUDA host-pinned memory (internal helper)
/// @internal
int cuda_host_free(void* host);

/// Register existing host buffer as CUDA pinned (internal helper)
/// @internal
int cuda_host_register(void* host, std::size_t bytes);

/// Unregister previously registered host buffer (internal helper)
/// @internal
int cuda_host_unregister(void* host);
