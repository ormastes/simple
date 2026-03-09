/**
 * @file mapper_host_impl.h
 * @brief Host-side implementation of the unified mapper interface
 *
 * Implements the Mapper<T> CRTP interface for host-side NVMe operations.
 * This provides host memory mapper, buffer pool management, and queue setup.
 */

#pragma once
#include "mapper/mapper.h"
#include "mapper_host.h"
#include "memory/host_memory_buffer.h"

class MapperInterface;

extern "C" {
HostPool* host_pool_create(NvmeDevice* d, uint16_t count, MapperInterface* mapping);
void host_pool_destroy(HostPool* p, MapperInterface* mapping);
DmaBuf* host_pool_acquire(HostPool* p);
void host_pool_release(HostPool* p, DmaBuf* b);
}

/**
 * @brief Host-side implementation of NVMe memory mapper
 *
 * Implements the Mapper<T> interface for host memory operations.
 * Provides VFIO-based DMA mapping, host buffer pools, and queue management.
 *
 * Features:
 * - VFIO DMA mapping for host pageable memory
 * - Pre-allocated buffer pools with PRP lists
 * - Host queue setup with command pools
 * - Support for both immediate and deferred doorbell modes
 */
class HostMapper : public Mapper<HostMapper> {
private:
    // Optional: Store any host-specific state here
    // Currently, operations are mostly stateless and use the device handle

public:
    HostMapper() = default;
    ~HostMapper() = default;

    // ========================================================================
    // Device Management (Non-template, called by runtime interface)
    // ========================================================================

    /**
     * @brief Open NVMe device via VFIO
     *
     * Initializes VFIO container, binds device, maps BAR, creates queues.
     *
     * @param bdf PCI BDF string
     * @param admin_qd Admin queue depth
     * @param io_qd I/O queue depth
     * @param item_size_bytes Transfer size in bytes
     * @return NvmeDevice handle on success, nullptr on failure
     */
    void* open_device(const char* bdf,
                      uint16_t admin_qd,
                      uint16_t io_qd,
                      uint32_t item_size_bytes) {
        return nvme_open(bdf, admin_qd, io_qd, item_size_bytes);
    }

    /**
     * @brief Close NVMe device and cleanup resources
     *
     * @param device Device handle from open_device
     */
    void close_device(void* device) {
        nvme_close(static_cast<NvmeDevice*>(device));
    }

    // ========================================================================
    // Queue Management
    // ========================================================================

    /**
     * @brief Setup queue for host operations
     *
     * @tparam QueueType Must be HOST_QUEUE (0) for host implementation
     * @param device Device handle
     * @param out_queue Output queue descriptor
     * @return 0 on success, -1 on failure
     */
    template<MemoryLocation Loc>
    int setup_queue(void* device, NvmeQueueStruct* out_queue) {
        static_assert(Loc == MemoryLocation::HOST,
                     "HostMapper only supports HOST queue");

        return nvme_setup_host_queue(static_cast<NvmeDevice*>(device),
                                     nullptr, out_queue);
    }

    /**
     * @brief Cleanup queue resources
     *
     * @param queue Queue descriptor to cleanup
     */
    void cleanup_queue(NvmeQueueStruct* queue) {
        nvme_cleanup_host_queue(queue);
    }

    /**
     * @brief Runtime dispatch for queue setup
     *
     * This method handles runtime dispatch without instantiating
     * invalid template specializations.
     *
     * @param device Device handle
     * @param queue_type Type of queue
     * @param out_queue Output queue descriptor
     * @return 0 on success, -1 on failure
     */
    int setup_queue_dispatch(void* device, uint8_t queue_type,
                            NvmeQueueStruct* out_queue) {
        if (queue_type == static_cast<uint8_t>(MemoryLocation::HOST)) {
            return this->template setup_queue<MemoryLocation::HOST>(device, out_queue);
        }
        // HostMapper only supports HOST queue
        return -1;
    }

    // ========================================================================
    // Memory Mapping
    // ========================================================================

    /**
     * @brief Map host memory for DMA operations
     *
     * @tparam Loc Memory location (must be HOST for host pageable memory)
     * @tparam Pin Pinning type (not used for host mapping)
     * @param device Device handle (used for VFIO container)
     * @param vaddr Virtual address to map
     * @param size Size in bytes
     * @param[out] iova Output IOVA address
     * @return 0 on success, -1 on failure
     */
    template<MemoryLocation Loc, Pinned Pin>
    int map_memory(void* device, void* vaddr, size_t size, uint64_t* iova) {
        static_assert(Loc == MemoryLocation::HOST,
                     "HostMapper only supports HOST memory");

        // Note: host_map_iova is a global function that uses the global
        // VFIO container, so device parameter is not directly used
        return host_map_iova(vaddr, size, iova);
    }

    /**
     * @brief Unmap previously mapped host memory
     *
     * @param device Device handle (used for VFIO container)
     * @param vaddr Virtual address
     * @param size Size in bytes
     * @param iova IOVA address to unmap
     * @return 0 on success, -1 on failure
     */
    int unmap_memory(void* device, void* vaddr, size_t size, uint64_t iova) {
        return host_unmap_iova(vaddr, size, iova);
    }

    /**
     * @brief Runtime dispatch for memory mapper
     *
     * @param device Device handle
     * @param vaddr Virtual address
     * @param size Size in bytes
     * @param[out] iova Output IOVA address
     * @return 0 on success, -1 on failure
     */
    int map_memory_dispatch(void* device, void* vaddr, size_t size,
                           uint64_t* iova) {
        // HostMapper only supports HOST memory
        return this->template map_memory<MemoryLocation::HOST, Pinned::NOT_PINNED>(device, vaddr, size, iova);
    }

    // ========================================================================
    // Buffer Pool Management
    // ========================================================================

    /**
     * @brief Create host memory buffer pool
     *
     * @tparam Loc Memory location (must be HOST for host memory pool)
     * @tparam Pin Pinning type (not used for host pool)
     * @param device Device handle
     * @param count Number of buffers
     * @return Pool handle on success, nullptr on failure
     */
    template<MemoryLocation Loc, Pinned Pin>
    HostPool* create_pool(void* device, uint16_t count) {
        static_assert(Loc == MemoryLocation::HOST,
                     "HostMapper only supports HOST pool");

        return host_pool_create(static_cast<NvmeDevice*>(device), count, nullptr);
    }

    /**
     * @brief Destroy buffer pool
     *
     * @param pool Pool handle to destroy
     */
    void destroy_pool(HostPool* pool) {
        host_pool_destroy(pool, nullptr);
    }

    /**
     * @brief Acquire buffer from pool
     *
     * @param pool Pool handle
     * @return Buffer on success, nullptr if pool full
     */
    DmaBuf* acquire_buffer(HostPool* pool) {
        return host_pool_acquire(pool);
    }

    /**
     * @brief Release buffer back to pool
     *
     * @param pool Pool handle
     * @param buffer Buffer to release
     */
    void release_buffer(HostPool* pool, DmaBuf* buffer) {
        host_pool_release(pool, buffer);
    }

    /**
     * @brief Runtime dispatch for pool creation
     *
     * This method handles runtime dispatch without instantiating
     * invalid template specializations.
     *
     * @param device Device handle
     * @param count Number of buffers
     * @param pool_type Type of pool
     * @return Pool handle on success, nullptr on failure
     */
    HostPool* create_pool_dispatch(void* device, uint16_t count,
                                  uint8_t pool_type) {
        if (pool_type == static_cast<uint8_t>(MemoryLocation::HOST)) {
            return this->template create_pool<MemoryLocation::HOST, Pinned::NOT_PINNED>(device, count);
        }
        // HostMapper only supports HOST pool
        return nullptr;
    }
};

// Register HostMapper as a valid mapping implementation
template<>
struct is_mapper<HostMapper> {
    static constexpr bool value = true;
};
