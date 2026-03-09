/**
 * @file cuda_io_host_mem.cpp
 * @brief Host-side implementation for cuda_io_host_mem
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

#include <cstdint>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <cstdio>
#include <vector>
#include <cuda_runtime_api.h>
#include "io/cuda_io_host_mem.h"
#include "memory/cuda_host_memory_buffer.h"
#include "cuda_utils.h"

namespace {
// Note: Page size should be obtained from NvmeDevice via nvme_get_page_size()
// when device context is available. This constant is only for fallback.
constexpr size_t kDefaultPageSize = 4096;

/// Round up size to alignment boundary
inline size_t round_up(size_t n, size_t a) {
    return (n + (a - 1)) & ~(a - 1);
}
} // namespace

extern "C" {

/// Allocate pinned (page-locked) host memory accessible by GPU
/// Memory allocated with this function is:
///  - Page-locked (won't be swapped out)
///  - DMA-capable for fast GPU transfers
///  - Portable across CUDA contexts
/// @param[out] out_host Pointer to store allocated memory address
/// @param bytes Number of bytes to allocate
/// @return 0 on success, -1 for invalid params, -2 for CUDA error
int cuda_host_alloc(void** out_host, size_t bytes){
  if (!out_host || bytes == 0) return -1;
  cudaError_t e = cudaHostAlloc(out_host, bytes, cudaHostAllocPortable);
  if (e != cudaSuccess) {
    std::fprintf(stderr, "cuda_host_alloc failed: %s\n", cudaGetErrorString(e));
    return -2;
  }
  return 0;
}

/// Free pinned host memory allocated with cuda_host_alloc
/// @param host Pointer to memory allocated by cuda_host_alloc
/// @return 0 on success, -1 for invalid params, -2 for CUDA error
int cuda_host_free(void* host){
  if (!host) return -1;
  cudaError_t e = cudaFreeHost(host);
  if (e != cudaSuccess) {
    std::fprintf(stderr, "cuda_host_free failed: %s\n", cudaGetErrorString(e));
    return -2;
  }
  return 0;
}

/// Register existing malloc'd memory as pinned (page-locked) for GPU access
/// This allows DMA transfers to/from pre-allocated memory.
/// Note: Cannot register memory already pinned by cuda_host_alloc.
/// @param host Pointer to malloc'd memory (must be page-aligned)
/// @param bytes Number of bytes to register
/// @return 0 on success, -1 for invalid params, -2 for CUDA error
int cuda_host_register(void* host, size_t bytes){
  if (!host || bytes == 0) return -1;
  cudaError_t e = cudaHostRegister(host, bytes, cudaHostRegisterPortable);
  if (e != cudaSuccess) {
    std::fprintf(stderr, "cuda_host_register failed: %s\n", cudaGetErrorString(e));
    return -2;
  }
  return 0;
}

/// Unregister previously registered host memory
/// After unregistering, memory can be freed with standard free()
/// @param host Pointer to memory registered by cuda_host_register
/// @return 0 on success, -1 for invalid params, -2 for CUDA error
int cuda_host_unregister(void* host){
  if (!host) return -1;
  cudaError_t e = cudaHostUnregister(host);
  if (e != cudaSuccess) {
    std::fprintf(stderr, "cuda_host_unregister failed: %s\n", cudaGetErrorString(e));
    return -2;
  }
  return 0;
}

// ============================================================================
// CUDA Host Memory IOVA Mapping (uses VFIO)
// ============================================================================

/// Map CUDA host-pinned memory to IOVA via VFIO
/// @param host CUDA host-pinned memory pointer
/// @param bytes Size in bytes
/// @param out_iova Pointer to store resulting IOVA
/// @return 0 on success, -1 on error
int cuda_host_map_iova(void* host, size_t bytes, uint64_t* out_iova) {
    // CUDA host-pinned memory uses same VFIO mapping as regular host memory
    return host_map_iova(host, bytes, out_iova);
}

/// Unmap CUDA host-pinned memory from IOVA via VFIO
/// @param host CUDA host-pinned memory pointer
/// @param bytes Size in bytes
/// @param iova IOVA address to unmap
/// @return 0 on success, -1 on error
int cuda_host_unmap_iova(void* host, size_t bytes, uint64_t iova) {
    // CUDA host-pinned memory uses same VFIO unmapping as regular host memory
    return host_unmap_iova(host, bytes, iova);
}

// ============================================================================
// CUDA Host Buffer Pool Implementation (Module 54.2)
// ============================================================================

/// Create pre-allocated pool of CUDA host-pinned buffers with VFIO DMA mapping
CudaHostPool* cuda_host_pool_create_ex(NvmeDevice* d, size_t buf_size, uint16_t count,
                                       PoolAllocMode mode) {
    if (!d || buf_size == 0 || count == 0) return nullptr;

    const size_t page_size = nvme_get_page_size(d);
    const size_t rounded_size = round_up(buf_size, page_size);
    const size_t pages = rounded_size / page_size;
    const size_t prplist_bytes = (pages > 2) ? round_up((pages - 1) * sizeof(uint64_t), page_size) : 0;
    const size_t chunk_size = rounded_size + prplist_bytes;
    const size_t total_size = chunk_size * count;

    // Allocate ONE block of pinned memory for all buffers
    // Use cudaHostAllocMapped when device shadow is needed so GPU can access the SAME memory
    void* pool_mem = nullptr;
    unsigned int alloc_flags = cudaHostAllocPortable;
    if (mode == PoolAllocMode::HOST_WITH_DEVICE_SHADOW) {
        alloc_flags |= cudaHostAllocMapped;  // Enable GPU mapping of host memory
    }
    cudaError_t e = cudaHostAlloc(&pool_mem, total_size, alloc_flags);
    if (e != cudaSuccess || !pool_mem) {
        std::fprintf(stderr, "ERROR: cuda_host_pool_create_ex() - cudaHostAlloc failed: %s\n",
                     cudaGetErrorString(e));
        return nullptr;
    }
    std::memset(pool_mem, 0, total_size);

    // Map entire pool to IOVA for NVMe DMA
    uint64_t pool_iova = 0;
    if (host_map_iova(pool_mem, total_size, &pool_iova) != 0) {
        std::fprintf(stderr, "ERROR: cuda_host_pool_create_ex() - Failed to map pool to IOVA\n");
        cudaFreeHost(pool_mem);
        return nullptr;
    }

    // Create pool and fill buffers
    auto* pool = new CudaHostPool();
    pool->dev = d;
    pool->buf_size = rounded_size;
    pool->cap = count;
    pool->alloc_mode = mode;
    pool->pool_iova = pool_iova;
    pool->total_size = total_size;
    pool->bufs.resize(count);

    // Split into individual buffers with proper IOVA offsets
    for (uint16_t i = 0; i < count; i++) {
        uint8_t* chunk_base = static_cast<uint8_t*>(pool_mem) + (i * chunk_size);
        void* addr = chunk_base;
        void* prplist = (prplist_bytes > 0) ? (chunk_base + rounded_size) : nullptr;

        uint64_t iova = pool_iova + (i * chunk_size);
        uint64_t prplist_iova_val = (prplist_bytes > 0) ? (iova + rounded_size) : 0;

        DmaBuf& buf = pool->bufs[i];
        buf.addr = addr;
        buf.bytes = rounded_size;
        buf.mem_type = MemoryType::PINNED_HOST;
        buf.item_size = ItemSize{static_cast<uint32_t>(rounded_size), 1, 1};
        buf.consecutive = Consecutive::NONE_CONSECUTIVE;
        buf.iova = iova;
        buf.prplist_host = prplist;
        buf.prplist_iova = prplist_iova_val;
        buf.prplist_bytes = prplist_bytes;
        nvme_buffer_impl::build_prps(buf.iova, buf.prplist_iova, buf.bytes, buf.prp1, buf.prp2);
    }

    return pool;
}

CudaHostPool* cuda_host_pool_create(NvmeDevice* d, size_t buf_size, uint16_t count) {
    return cuda_host_pool_create_ex(d, buf_size, count, PoolAllocMode::HOST_ONLY);
}

/// Acquire buffer from pool (non-blocking)
DmaBuf* cuda_host_pool_acquire(CudaHostPool* p) {
    if (!p) return nullptr;
    DmaBuf* buf = p->acquire();
    if (!buf) return nullptr;

    // Get device pointer to the SAME host memory (not a separate allocation)
    // This allows GPU to access the same physical memory that NVMe DMAs to
    if (p->alloc_mode == PoolAllocMode::HOST_WITH_DEVICE_SHADOW && buf->device_alias == nullptr) {
        void* dev_ptr = nullptr;
        cudaError_t e = cudaHostGetDevicePointer(&dev_ptr, buf->addr, 0);
        if (e != cudaSuccess) {
            std::fprintf(stderr, "cuda_host_pool_acquire: cudaHostGetDevicePointer failed: %s\n",
                         cudaGetErrorString(e));
            return nullptr;
        }
        buf->device_alias = dev_ptr;
    }
    return buf;
}

/// Release buffer back to pool
void cuda_host_pool_release(CudaHostPool* p, DmaBuf* b) {
    if (!p || !b) return;
    // Use Pool template's release method directly
    p->release(b);
}

/// Destroy pool and free all buffers
void cuda_host_pool_destroy(CudaHostPool* p) {
    if (!p) return;

    // device_alias is a device pointer to the same host memory (via cudaHostGetDevicePointer)
    // so we do NOT call cuda_free on it - the memory is freed when pool_mem is freed
    // Just clear the pointers
    if (p->alloc_mode == PoolAllocMode::HOST_WITH_DEVICE_SHADOW) {
        for (auto& buf : p->bufs) {
            buf.device_alias = nullptr;
        }
    }
    // Use standard delete for Pool template
    delete p;
}

// ============================================================================
// CUDA Host Pinned Consecutive Buffer (Module 54.3)
// ============================================================================

/// Create CUDA host-pinned consecutive buffer with VFIO DMA mapping
Buffer* cuda_host_create_pinned_consecutive_buffer(size_t buffer_size) {
    if (buffer_size == 0) return nullptr;

    // Allocate CUDA host-pinned memory
    void* host = nullptr;
    if (cuda_host_alloc(&host, buffer_size) != 0) {
        std::fprintf(stderr, "cuda_host_alloc failed for %zu bytes\n", buffer_size);
        return nullptr;
    }

    // Map for DMA (assumes NVMe device has been opened and global mapping state exists)
    uint64_t iova = 0;
    if (host_map_iova(host, buffer_size, &iova) != 0) {
        std::fprintf(stderr, "host_map_iova failed\n");
        cuda_host_free(host);
        return nullptr;
    }

    // Create buffer descriptor
    Buffer* b = new Buffer();
    b->addr = host;
    b->bytes = buffer_size;
    b->iova = iova;
    b->mem_type = MemoryType::PINNED_HOST;
    b->consecutive = Consecutive::CONSECUTIVE;

    return b;
}

/// Destroy CUDA host-pinned buffer
void cuda_host_buffer_destroy(Buffer* b) {
    if (!b) return;

    if (b->addr) {
        host_unmap_iova(b->addr, b->bytes, b->iova);
        cuda_host_free(b->addr);
    }

    delete b;
}

// ============================================================================
// Unified Command Submission API (Module 54.4)
// ============================================================================

/// Runtime dispatch wrapper for CUDA host-pinned buffers
/// Thin wrapper around Module 53's host_submit_runtime()
uint16_t cuda_host_submit_runtime(CommandType cmd_type, const DoorbellHandle* doorbell,
                                        Queue* iosq, uint32_t nsid,
                                        uint64_t slba, uint32_t lba_size,
                                        DmaBuf* b, size_t bytes) {
    return host_submit_runtime(cmd_type, doorbell, iosq, nsid, slba, lba_size, b, bytes);
}

// ============================================================================
// Completion Polling API (Module 54.5)
// ============================================================================

/// Runtime dispatch wrapper for completion polling
/// Thin wrapper around Module 53's host_poll_completion_runtime()
NvmeStatus cuda_host_poll_completion_runtime(AsyncType async_type, Queue* iocq,
                                              uint16_t* out_cid,
                                              PollResult* out_poll_result,
                                              uint32_t timeout_us,
                                              Queue* iosq) {
    // Direct passthrough to Module 53's implementation
    // Completion polling is independent of buffer type
    return host_poll_completion_runtime(async_type, iocq, out_cid, out_poll_result, timeout_us, iosq);
}

} // extern "C"
