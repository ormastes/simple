/**
 * @file forward_decls.h
 * @brief Central forward declarations for commonly used types
 *
 * This header provides forward declarations for types that are frequently
 * referenced across multiple modules. Include this header instead of
 * duplicating forward declarations in individual files.
 */

#pragma once

// ============================================================================
// Device and Queue Types
// ============================================================================

/// NVMe device handle (defined in host/mapper/mapper_host.cpp)
struct NvmeDevice;

/// NVMe queue structure (defined in common/queue/nvme_queue.h)
struct NvmeQueueStruct;

// ============================================================================
// Memory Pool Types
// ============================================================================

/// Base pool structure (defined in common/memory/memory_pool.h)
struct PoolStruct;

/// Host memory pool (defined in common/memory/memory_pool.h)
/// Note: HostPool is actually a struct, not just a type alias
struct HostPool;

/// CUDA host memory pool (defined in common/memory/memory_pool.h)
struct CudaHostPool;

/// GPU device memory pool (defined in common/memory/memory_pool.h)
struct CudaGpuPool;

// ============================================================================
// Mapping Interface
// ============================================================================

/// Mapping interface for device operations (defined in common/mapper/mapper.h)
class MapperInterface;

// ============================================================================
// Usage Notes
// ============================================================================
//
// Instead of:
//   struct NvmeDevice;  // Duplicated in every file
//
// Do:
//   #include "forward_decls.h"
//
