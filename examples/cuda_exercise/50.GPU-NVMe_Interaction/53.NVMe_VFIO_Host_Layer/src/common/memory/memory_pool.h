/**
 * @file memory_pool.h
 * @brief Memory pool management for DMA buffers.
 *
 * This header now owns the shared DMA buffer types plus the template-based
 * pool helpers and buffer-construction utilities that used to live in
 * memory_buffer_impl.h.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#include <thrust/device_vector.h>
#include <thrust/host_vector.h>

#include "memory/memory_types.h"
#include "mapper/mapper.h"
#include "../host/mapper/mapper_host.h"
#include "forward_decls.h"
#include "cuda_utils.h"

struct PoolStruct {};

/// Pool allocation mode to signal optional helpers (e.g., host pool with GPU shadow)
enum class PoolAllocMode : uint8_t {
    HOST_ONLY = 0,
    HOST_WITH_DEVICE_SHADOW = 1
};

// ============================================================================
// Memory Pool Template (circular buffer with acquire/release)
// ============================================================================

/// Pool template: circular buffer with acquire/release (host and GPU)
/// @tparam VectorType Container type (std::vector, thrust::host_vector, thrust::device_vector)
template<typename VectorType>
struct Pool : public PoolStruct {
    NvmeDevice*  dev{nullptr};        ///< NVMe device handle
    MapperInterface* mapper{nullptr}; ///< Mapper for IOVA mapping/unmapping
    size_t  buf_size{0};              ///< Buffer size in bytes
    size_t  total_size{0};            ///< Total pool allocation size
    uint64_t pool_iova{0};            ///< Base IOVA for pool
    uint16_t cap{0};                  ///< Pool capacity
    uint16_t head{0};                 ///< Acquire index
    uint16_t tail{0};                 ///< Release index
    uint16_t in_use{0};               ///< Buffers currently acquired
    PoolAllocMode alloc_mode{PoolAllocMode::HOST_ONLY}; ///< Optional behavior flags
    VectorType   bufs;                ///< DMA buffer storage

    virtual ~Pool() {
        // Unmap pool memory (NullMapper does nothing for GPU)
        if (mapper && !bufs.empty() && bufs[0].addr) {
            mapper->unmap_memory_runtime(dev, bufs[0].addr, total_size, pool_iova);
        }
    }

    /// Acquire buffer (nullptr if full)
    __device__ __host__ inline DmaBuf* acquire() {
        if (in_use >= cap) return nullptr;
        DmaBuf* buf = &bufs[head];
        head = (head + 1) % cap;
        in_use++;
        return buf;
    }

    /// Release buffer
    __device__ __host__ inline void release(DmaBuf* b) {
        if (!b || in_use == 0) return;
        tail = (tail + 1) % cap;
        in_use--;
    }

    __device__ __host__ inline bool is_full() const { return in_use >= cap; }
    __device__ __host__ inline bool is_empty() const { return in_use == 0; }
    __device__ __host__ inline uint16_t available() const { return cap - in_use; }
};

// ============================================================================
// Concrete Pool Types
// ============================================================================

/// Host pool using std::vector (Module 53 - pageable memory)
struct HostPool : public Pool<std::vector<DmaBuf>> {
    using Pool<std::vector<DmaBuf>>::Pool;
};

/// CUDA host pool using thrust::host_vector (Module 54 - pinned memory)
struct CudaHostPool : public Pool<thrust::host_vector<DmaBuf>> {
    using Pool<thrust::host_vector<DmaBuf>>::Pool;
};

/// GPU pool using thrust::device_vector (Module 55, 56)
struct CudaGpuPool : public Pool<thrust::device_vector<DmaBuf>> {
    using Pool<thrust::device_vector<DmaBuf>>::Pool;
};

// ============================================================================
// Buffer construction helpers (formerly memory_buffer_impl.h)
// ============================================================================

namespace nvme_buffer_impl {

inline size_t round_up(size_t n, size_t alignment) {
    return (n + (alignment - 1)) & ~(alignment - 1);
}

inline void* page_alloc(size_t bytes) {
    void* ptr = nullptr;
    if (posix_memalign(&ptr, 4096, bytes) != 0) {
        return nullptr;
    }
    std::memset(ptr, 0, bytes);
    return ptr;
}

inline void build_prps(uint64_t iova, uint64_t prplist_iova, size_t bytes,
                       uint64_t& prp1, uint64_t& prp2) {
    constexpr size_t kPage = 4096;
    const size_t pages = (bytes + kPage - 1) / kPage;

    prp1 = iova;  // First page always goes in PRP1

    if (pages == 1) {
        prp2 = 0;  // Single page, no PRP2
    } else if (pages == 2) {
        prp2 = iova + kPage;  // Two pages, PRP2 points to second page
    } else {
        prp2 = prplist_iova;  // Multi-page, PRP2 points to PRP list
    }
}

template<typename VectorType>
int fill_pool_buffers(VectorType& bufs,
                      NvmeDevice* dev,
                      const ItemSize& item_size,
                      uint16_t count,
                      MemoryType mem_type,
                      MapperInterface* mapping = nullptr);

template<>
inline int fill_pool_buffers<std::vector<DmaBuf>>(std::vector<DmaBuf>& bufs,
                                                  NvmeDevice* dev,
                                                  const ItemSize& item_size,
                                                  uint16_t count,
                                                  MemoryType mem_type,
                                                  MapperInterface* mapping) {
    // NullMapper: No-op for GPU device memory (no IOVA mapping needed)
    static class NullMapper : public MapperInterface {
    public:
        void* open_device_runtime(const char*, uint16_t, uint16_t, uint32_t) override { return nullptr; }
        void close_device_runtime(void*) override {}
        int setup_queue_runtime(void*, uint8_t, NvmeQueueStruct*) override { return 0; }
        void cleanup_queue_runtime(NvmeQueueStruct*) override {}
        int map_memory_runtime(void*, void*, size_t, uint64_t* iova) override {
            if (iova) *iova = 0;  // GPU memory doesn't need IOVA mapping
            return 0;
        }
        int unmap_memory_runtime(void*, void*, size_t, uint64_t) override {
            return 0;  // No-op
        }
        HostPool* create_pool_runtime(void*, uint16_t, uint8_t) override { return nullptr; }
        void destroy_pool_runtime(HostPool*) override {}
        DmaBuf* acquire_buffer_runtime(HostPool*) override { return nullptr; }
        void release_buffer_runtime(HostPool*, DmaBuf*) override {}
    } null_mapper;

    // DefaultHostMapping: Uses VFIO for host/pinned-host memory
    static class DefaultHostMapping : public MapperInterface {
    public:
        void* open_device_runtime(const char*, uint16_t, uint16_t, uint32_t) override { return nullptr; }
        void close_device_runtime(void*) override {}
        int setup_queue_runtime(void*, uint8_t, NvmeQueueStruct*) override { return -1; }
        void cleanup_queue_runtime(NvmeQueueStruct*) override {}
        int map_memory_runtime(void*, void* vaddr, size_t size, uint64_t* iova) override {
            return host_map_iova(vaddr, size, iova);
        }
        int unmap_memory_runtime(void*, void* vaddr, size_t size, uint64_t iova) override {
            return host_unmap_iova(vaddr, size, iova);
        }
        HostPool* create_pool_runtime(void*, uint16_t, uint8_t) override { return nullptr; }
        void destroy_pool_runtime(HostPool*) override {}
        DmaBuf* acquire_buffer_runtime(HostPool*) override { return nullptr; }
        void release_buffer_runtime(HostPool*, DmaBuf*) override {}
    } default_mapping;

    // Select mapper based on memory type
    if (!mapping) {
        if (mem_type == MemoryType::PINNED_DEVICE) {
            mapping = &null_mapper;
        } else {
            mapping = &default_mapping;
        }
    }

    const size_t page_size = nvme_get_page_size(dev);
    const size_t buf_size = item_size.total_size;
    const size_t pages = buf_size / page_size;
    const size_t prplist_bytes = (pages > 2) ? round_up((pages - 1) * sizeof(uint64_t), page_size) : 0;

    // Calculate total size: (buffer + PRP) * count in ONE allocation
    const size_t chunk_size = buf_size + prplist_bytes;
    const size_t total_size = chunk_size * count;

    // Allocate ONE contiguous block for all buffers and PRP lists
    void* pool_mem = nullptr;
    if (mem_type == MemoryType::HOST) {
        pool_mem = page_alloc(total_size);
    } else if (mem_type == MemoryType::PINNED_HOST) {
#ifdef __CUDACC__
        CHECK_CUDA(cudaHostAlloc(&pool_mem, total_size, cudaHostAllocPortable));
        std::memset(pool_mem, 0, total_size);
#else
        std::fprintf(stderr, "ERROR: fill_pool_buffers() - MemoryType::PINNED_HOST requires CUDA\n");
        return -1;
#endif
    } else if (mem_type == MemoryType::PINNED_DEVICE) {
#ifdef __CUDACC__
        pool_mem = cuda_calloc<uint8_t>(total_size);
#else
        std::fprintf(stderr, "ERROR: fill_pool_buffers() - MemoryType::PINNED_DEVICE requires CUDA\n");
        return -1;
#endif
    } else {
        std::fprintf(stderr, "ERROR: fill_pool_buffers() - Unsupported memory type\n");
        return -1;
    }

    if (!pool_mem) {
        std::fprintf(stderr, "ERROR: fill_pool_buffers() - Failed to allocate pool memory (%zu bytes)\n", total_size);
        return -1;
    }

    // Map entire pool ONCE (NullMapper does nothing for GPU memory)
    uint64_t pool_iova = 0;
    if (mapping->map_memory_runtime(dev, pool_mem, total_size, &pool_iova) != 0) {
        std::fprintf(stderr, "ERROR: fill_pool_buffers() - Failed to map pool to IOVA\n");
        if (mem_type == MemoryType::HOST) std::free(pool_mem);
#ifdef __CUDACC__
        else if (mem_type == MemoryType::PINNED_HOST) cudaFreeHost(pool_mem);
        else cuda_free(pool_mem);
#endif
        return -1;
    }

    // Split memory into buffers and PRP lists
    for (uint16_t i = 0; i < count; i++) {
        uint8_t* chunk_base = static_cast<uint8_t*>(pool_mem) + (i * chunk_size);
        void* addr = chunk_base;
        void* prplist = (prplist_bytes > 0) ? (chunk_base + buf_size) : nullptr;

        uint64_t iova = pool_iova + (i * chunk_size);
        uint64_t prplist_iova = (prplist_bytes > 0) ? (iova + buf_size) : 0;

        DmaBuf& buf = bufs[i];
        buf.addr = addr;
        buf.bytes = buf_size;
        buf.mem_type = mem_type;
        buf.item_size = item_size;
        buf.consecutive = Consecutive::NONE_CONSECUTIVE;
        buf.iova = iova;
        buf.prplist_host = prplist;
        buf.prplist_iova = prplist_iova;
        buf.prplist_bytes = prplist_bytes;
        build_prps(buf.iova, buf.prplist_iova, buf.bytes, buf.prp1, buf.prp2);
    }

    return 0;
}

#ifdef __CUDACC__
template<>
inline int fill_pool_buffers<thrust::host_vector<DmaBuf>>(thrust::host_vector<DmaBuf>& bufs,
                                                          NvmeDevice* dev,
                                                          const ItemSize& item_size,
                                                          uint16_t count,
                                                          MemoryType mem_type,
                                                          MapperInterface* mapping) {
    const size_t page_size = dev ? nvme_get_page_size(dev) : 4096;
    const size_t buf_size = item_size.total_size;
    const size_t pages = buf_size / page_size;
    const size_t prplist_bytes = (pages > 2) ? round_up((pages - 1) * sizeof(uint64_t), page_size) : 0;
    const size_t chunk_size = buf_size + prplist_bytes;
    const size_t total_size = chunk_size * count;

    // Allocate ONE block for all buffers
    void* pool_mem = nullptr;
    if (mem_type == MemoryType::HOST) {
        pool_mem = page_alloc(total_size);
    } else if (mem_type == MemoryType::PINNED_HOST) {
        CHECK_CUDA(cudaHostAlloc(&pool_mem, total_size, cudaHostAllocPortable));
        std::memset(pool_mem, 0, total_size);
    } else if (mem_type == MemoryType::PINNED_DEVICE) {
        pool_mem = cuda_calloc<uint8_t>(total_size);
    } else {
        std::fprintf(stderr, "ERROR: fill_pool_buffers(thrust) - Unsupported memory type\n");
        return -1;
    }

    if (!pool_mem) {
        std::fprintf(stderr, "ERROR: fill_pool_buffers(thrust) - Failed to allocate pool (%zu bytes)\n", total_size);
        return -1;
    }

    // Map entire pool to IOVA for HOST and PINNED_HOST (NVMe DMA requires IOVA)
    uint64_t pool_iova = 0;
    if ((mem_type == MemoryType::HOST || mem_type == MemoryType::PINNED_HOST) && dev) {
        if (mapping) {
            if (mapping->map_memory_runtime(dev, pool_mem, total_size, &pool_iova) != 0) {
                std::fprintf(stderr, "ERROR: fill_pool_buffers(thrust) - Failed to map pool to IOVA\n");
                if (mem_type == MemoryType::HOST) std::free(pool_mem);
                else cudaFreeHost(pool_mem);
                return -1;
            }
        } else {
            // Use default host mapping
            if (host_map_iova(pool_mem, total_size, &pool_iova) != 0) {
                std::fprintf(stderr, "ERROR: fill_pool_buffers(thrust) - Failed to map pool to IOVA\n");
                if (mem_type == MemoryType::HOST) std::free(pool_mem);
                else cudaFreeHost(pool_mem);
                return -1;
            }
        }
    }

    // Split into individual buffers with proper IOVA offsets
    for (uint16_t i = 0; i < count; i++) {
        uint8_t* chunk_base = static_cast<uint8_t*>(pool_mem) + (i * chunk_size);
        void* addr = chunk_base;
        void* prplist = (prplist_bytes > 0) ? (chunk_base + buf_size) : nullptr;

        uint64_t iova = pool_iova + (i * chunk_size);
        uint64_t prplist_iova_val = (prplist_bytes > 0) ? (iova + buf_size) : 0;

        DmaBuf& buf = bufs[i];
        buf.addr = addr;
        buf.bytes = buf_size;
        buf.mem_type = mem_type;
        buf.item_size = item_size;
        buf.consecutive = Consecutive::NONE_CONSECUTIVE;
        buf.iova = iova;
        buf.prplist_host = prplist;
        buf.prplist_iova = prplist_iova_val;
        buf.prplist_bytes = prplist_bytes;
        build_prps(buf.iova, buf.prplist_iova, buf.bytes, buf.prp1, buf.prp2);
    }

    return 0;
}
#endif  // __CUDACC__

}  // namespace nvme_buffer_impl
