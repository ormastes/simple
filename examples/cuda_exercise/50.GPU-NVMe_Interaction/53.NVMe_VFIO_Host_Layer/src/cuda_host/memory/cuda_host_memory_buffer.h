/**
 * @file cuda_host_memory_buffer.h
 * @brief CUDA host-pinned memory buffer pool management for NVMe DMA operations
 *
 * Provides buffer pool allocation with CUDA host-pinned memory, VFIO DMA mapping,
 * and consecutive buffer creation (Module 54).
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cassert>
#include "memory/memory_pool.h"  // For DmaBuf, Pool, Buffer
#include "forward_decls.h"

extern "C" {

// ============================================================================
// CUDA Host Memory Allocation Functions
// ============================================================================

// Allocate CUDA host-pinned memory; returns 0 on success.
int  cuda_host_alloc(void** out_host, size_t bytes);
// Free CUDA host-pinned memory.
int  cuda_host_free(void* host);
// Register an existing host buffer as CUDA pinned.
int  cuda_host_register(void* host, size_t bytes);
// Unregister a previously registered host buffer.
int  cuda_host_unregister(void* host);

// ============================================================================
// CUDA Host Memory Mapping Functions
// ============================================================================

/// Map CUDA host-pinned memory to IOVA via VFIO
int cuda_host_map_iova(void* host, size_t bytes, uint64_t* out_iova);

/// Unmap CUDA host-pinned memory from IOVA via VFIO
int cuda_host_unmap_iova(void* host, size_t bytes, uint64_t iova);

// ============================================================================
// CUDA Host Memory Buffer Pool API (Module 54)
// ============================================================================

/// Create pre-allocated pool of CUDA host-pinned buffers with VFIO DMA mapping
///
/// @param d NVMe device handle (for VFIO DMA mapping)
/// @param buf_size Size of each buffer in bytes (will be page-aligned)
/// @param count Number of buffers in pool
/// @return Pool handle, or nullptr on failure
CudaHostPool* cuda_host_pool_create(NvmeDevice* d, size_t buf_size, uint16_t count);
CudaHostPool* cuda_host_pool_create_ex(NvmeDevice* d, size_t buf_size, uint16_t count,
                                       PoolAllocMode mode);

/// Acquire buffer from pool (non-blocking)
///
/// @param p Pool handle
/// @return DmaBuf with CUDA host-pinned memory, or nullptr if pool full
DmaBuf* cuda_host_pool_acquire(CudaHostPool* p);

/// Release buffer back to pool
///
/// @param p Pool handle
/// @param b Buffer to release (can be nullptr)
void cuda_host_pool_release(CudaHostPool* p, DmaBuf* b);

/// Destroy pool and free all buffers
///
/// @param p Pool handle
void cuda_host_pool_destroy(CudaHostPool* p);

// ============================================================================
// CUDA Host Consecutive Buffer API (Module 54.3)
// ============================================================================

/// Create CUDA host-pinned consecutive buffer with VFIO DMA mapping
///
/// @param buffer_size Size of buffer in bytes (will be page-aligned)
/// @return Buffer descriptor, or nullptr on failure
Buffer* cuda_host_create_pinned_consecutive_buffer(size_t buffer_size);

/// Destroy CUDA host-pinned buffer
///
/// @param b Buffer to destroy
void cuda_host_buffer_destroy(Buffer* b);

} // extern "C"
