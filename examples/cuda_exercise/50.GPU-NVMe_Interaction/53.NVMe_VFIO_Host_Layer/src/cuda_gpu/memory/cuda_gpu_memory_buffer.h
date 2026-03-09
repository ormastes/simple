/**
 * @file cuda_gpu_memory_buffer.h
 * @brief GPU device memory buffer pool management for NVMe DMA operations
 *
 * Provides buffer pool allocation with GPU device memory, P2P DMA mapping,
 * and consecutive buffer creation (Module 55).
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include <cassert>
#include "memory/memory_pool.h"  // For DmaBuf, Pool, Buffer, IovaSeg
#include "forward_decls.h"

extern "C" {

// ============================================================================
// GPU Device Memory Buffer Pool API (Module 55)
// ============================================================================

/// Create pre-allocated pool of GPU device memory buffers with P2P DMA mapping
///
/// @param d NVMe device handle (for device association)
/// @param buf_size Size of each buffer in bytes (will be page-aligned)
/// @param count Number of buffers in pool
/// @return Pool handle, or nullptr on failure
///
/// Note: Requires GPU P2P kernel module for IOVA mapping in real implementation
__host__ CudaGpuPool* cuda_gpu_pool_create(NvmeDevice* d, size_t buf_size, uint16_t count);

/// Acquire buffer from pool (non-blocking)
///
/// @param p Pool handle
/// @return DmaBuf with GPU device memory, or nullptr if pool full
__host__ DmaBuf* cuda_gpu_pool_acquire(CudaGpuPool* p);

/// Release buffer back to pool
///
/// @param p Pool handle
/// @param b Buffer to release (can be nullptr)
__host__ void cuda_gpu_pool_release(CudaGpuPool* p, DmaBuf* b);

/// Destroy pool and free all buffers
///
/// @param p Pool handle
__host__ void cuda_gpu_pool_destroy(CudaGpuPool* p);

// ============================================================================
// GPU Device Consecutive Buffer API (Module 55.3)
// ============================================================================

/// Create GPU device memory consecutive buffer with P2P DMA mapping
///
/// @param buffer_size Size of buffer in bytes (will be page-aligned)
/// @return Buffer descriptor, or nullptr on failure
///
/// Note: This is a STUB - requires kernel module for real P2P mapping
__host__ Buffer* cuda_gpu_create_device_consecutive_buffer(size_t buffer_size);

/// Destroy GPU device memory buffer
///
/// @param b Buffer to destroy
__host__ void cuda_gpu_buffer_destroy(Buffer* b);

} // extern "C"
