/**
 * @file mapper.h
 * @brief Unified mapper interface for host and GPU NVMe memory operations
 *
 * This file provides:
 * - MapperInterface: Virtual interface for runtime polymorphism (host-only)
 * - Mapper<T>: CRTP base class for compile-time polymorphism (host and GPU)
 * - Common mapper operations for NVMe memory management
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include "nvme_types.h"
#include "queue/nvme_queue.h"
#include "memory/memory_types.h"

struct HostPool;

// CUDA compatibility macros
#ifndef __CUDACC__
    #ifndef __device__
        #define __device__
    #endif
    #ifndef __host__
        #define __host__
    #endif
#endif

// ============================================================================
// Host-Only Virtual Interface (Runtime Polymorphism)
// ============================================================================

/**
 * @brief Abstract base class for NVMe memory mapper operations
 *
 * Provides virtual interface for runtime dispatch of mapper operations.
 * This is host-only as virtual functions cannot be used in device code.
 *
 * Implementations should provide:
 * - Device initialization and cleanup
 * - Queue setup and management
 * - Memory mapper (DMA, P2P)
 * - Buffer pool management
 */
class MapperInterface {
public:
    virtual ~MapperInterface() = default;

    // Prevent copying
    MapperInterface(const MapperInterface&) = delete;
    MapperInterface& operator=(const MapperInterface&) = delete;

    // ========================================================================
    // Device Management
    // ========================================================================

    /**
     * @brief Open NVMe device and initialize
     *
     * @param bdf PCI BDF string (e.g., "0000:01:00.0")
     * @param admin_qd Admin queue depth
     * @param io_qd I/O queue depth
     * @param item_size_bytes Transfer size in bytes
     * @return Device handle on success, nullptr on failure
     */
    virtual void* open_device_runtime(const char* bdf,
                                      uint16_t admin_qd,
                                      uint16_t io_qd,
                                      uint32_t item_size_bytes) = 0;

    /**
     * @brief Close device and cleanup resources
     *
     * @param device Device handle from open_device_runtime
     */
    virtual void close_device_runtime(void* device) = 0;

    // ========================================================================
    // Queue Management
    // ========================================================================

    /**
     * @brief Setup queue for host or GPU operations
     *
     * @param device Device handle
     * @param queue_type Type of queue (host/GPU)
     * @param out_queue Output queue descriptor
     * @return 0 on success, -1 on failure
     */
    virtual int setup_queue_runtime(void* device,
                                    uint8_t queue_type,
                                    NvmeQueueStruct* out_queue) = 0;

    /**
     * @brief Cleanup queue resources
     *
     * @param queue Queue descriptor to cleanup
     */
    virtual void cleanup_queue_runtime(NvmeQueueStruct* queue) = 0;

    // ========================================================================
    // Memory Mapping
    // ========================================================================

    /**
     * @brief Map memory for DMA operations
     *
     * @param device Device handle
     * @param vaddr Virtual address to map
     * @param size Size in bytes
     * @param[out] iova Output IOVA address
     * @return 0 on success, -1 on failure
     */
    virtual int map_memory_runtime(void* device,
                                   void* vaddr,
                                   size_t size,
                                   uint64_t* iova) = 0;

    /**
     * @brief Unmap previously mapped memory
     *
     * @param device Device handle
     * @param vaddr Virtual address
     * @param size Size in bytes
     * @param iova IOVA address to unmap
     * @return 0 on success, -1 on failure
     */
    virtual int unmap_memory_runtime(void* device,
                                     void* vaddr,
                                     size_t size,
                                     uint64_t iova) = 0;

    // ========================================================================
    // Buffer Pool Management
    // ========================================================================

    /**
     * @brief Create buffer pool for DMA operations
     *
     * @param device Device handle
     * @param count Number of buffers
     * @param pool_type Type of pool (host/pinned/GPU)
     * @return Pool handle on success, nullptr on failure
     */
    virtual HostPool* create_pool_runtime(void* device,
                                         uint16_t count,
                                         uint8_t pool_type) = 0;

    /**
     * @brief Destroy buffer pool
     *
     * @param pool Pool handle to destroy
     */
    virtual void destroy_pool_runtime(HostPool* pool) = 0;

    /**
     * @brief Acquire buffer from pool
     *
     * @param pool Pool handle
     * @return Buffer on success, nullptr if pool full
     */
    virtual DmaBuf* acquire_buffer_runtime(HostPool* pool) = 0;

    /**
     * @brief Release buffer back to pool
     *
     * @param pool Pool handle
     * @param buffer Buffer to release
     */
    virtual void release_buffer_runtime(HostPool* pool, DmaBuf* buffer) = 0;

protected:
    MapperInterface() = default;
};

// ============================================================================
// CRTP Base Class (Compile-Time Polymorphism, Host and GPU)
// ============================================================================

/**
 * @brief CRTP base class for compile-time polymorphic mapper operations
 *
 * @tparam Derived The derived class implementing actual mapper logic
 *
 * This template provides compile-time dispatch for mapper operations
 * and works on both host and GPU. The derived class must implement
 * the actual mapper functions.
 *
 * Example usage:
 * @code
 * class HostMapper : public Mapper<HostMapper> {
 *     // Implement mapper operations
 * };
 *
 * class GpuMapper : public Mapper<GpuMapper> {
 *     // Implement GPU mapper operations
 * };
 * @endcode
 */
template<typename Derived>
class Mapper : public MapperInterface {
public:
    // ========================================================================
    // Template-based Operations (Compile-time dispatch)
    // ========================================================================

    /**
     * @brief Map memory for DMA (compile-time dispatch)
     *
     * @tparam Loc Memory location (MemoryLocation::HOST or MemoryLocation::DEVICE)
     * @tparam Pin Pinning type (Pinned::NOT_PINNED or Pinned::PINNED)
     * @param device Device handle
     * @param vaddr Virtual address
     * @param size Size in bytes
     * @param[out] iova Output IOVA address
     * @return 0 on success, -1 on failure
     */
    template<MemoryLocation Loc, Pinned Pin>
    __device__ __host__ inline int map_memory(void* device,
                                              void* vaddr,
                                              size_t size,
                                              uint64_t* iova) {
        return static_cast<Derived*>(this)->template map_memory<Loc, Pin>(
            device, vaddr, size, iova);
    }

    /**
     * @brief Create buffer pool (compile-time dispatch)
     *
     * @tparam Loc Memory location (MemoryLocation::HOST or MemoryLocation::DEVICE)
     * @tparam Pin Pinning type (Pinned::NOT_PINNED or Pinned::PINNED)
     * @param device Device handle
     * @param count Number of buffers
     * @return Pool handle on success, nullptr on failure
     */
    template<MemoryLocation Loc, Pinned Pin>
    __device__ __host__ inline HostPool* create_pool(void* device,
                                                    uint16_t count) {
        return static_cast<Derived*>(this)->template create_pool<Loc, Pin>(
            device, count);
    }

    /**
     * @brief Setup queue (compile-time dispatch)
     *
     * @tparam Loc Queue location (MemoryLocation::HOST or MemoryLocation::DEVICE)
     * @param device Device handle
     * @param out_queue Output queue descriptor
     * @return 0 on success, -1 on failure
     */
    template<MemoryLocation Loc>
    __device__ __host__ inline int setup_queue(void* device,
                                               NvmeQueueStruct* out_queue) {
        return static_cast<Derived*>(this)->template setup_queue<Loc>(
            device, out_queue);
    }

    void* open_device_runtime(const char* bdf,
                              uint16_t admin_qd,
                              uint16_t io_qd,
                              uint32_t item_size_bytes) override {
        return static_cast<Derived*>(this)->open_device(
            bdf, admin_qd, io_qd, item_size_bytes);
    }

    void close_device_runtime(void* device) override {
        static_cast<Derived*>(this)->close_device(device);
    }

    int setup_queue_runtime(void* device,
                           uint8_t queue_type,
                           NvmeQueueStruct* out_queue) override {
        // Delegate to derived class for runtime dispatch
        return static_cast<Derived*>(this)->setup_queue_dispatch(
            device, queue_type, out_queue);
    }

    void cleanup_queue_runtime(NvmeQueueStruct* queue) override {
        static_cast<Derived*>(this)->cleanup_queue(queue);
    }

    int map_memory_runtime(void* device,
                          void* vaddr,
                          size_t size,
                          uint64_t* iova) override {
        // Delegate to derived class for runtime dispatch
        return static_cast<Derived*>(this)->map_memory_dispatch(
            device, vaddr, size, iova);
    }

    int unmap_memory_runtime(void* device,
                            void* vaddr,
                            size_t size,
                            uint64_t iova) override {
        return static_cast<Derived*>(this)->unmap_memory(
            device, vaddr, size, iova);
    }

    HostPool* create_pool_runtime(void* device,
                                 uint16_t count,
                                 uint8_t pool_type) override {
        // Delegate to derived class for runtime dispatch
        return static_cast<Derived*>(this)->create_pool_dispatch(
            device, count, pool_type);
    }

    void destroy_pool_runtime(HostPool* pool) override {
        static_cast<Derived*>(this)->destroy_pool(pool);
    }

    DmaBuf* acquire_buffer_runtime(HostPool* pool) override {
        return static_cast<Derived*>(this)->acquire_buffer(pool);
    }

    void release_buffer_runtime(HostPool* pool, DmaBuf* buffer) override {
        static_cast<Derived*>(this)->release_buffer(pool, buffer);
    }
protected:
    ~Mapper() = default;
};

// ============================================================================
// Buffer Type Enums (from memory/memory_buffer.h)
// ============================================================================

// Note: Buffer type enums are defined in memory/memory_buffer.h:
// - enum class MemoryLocation: HOST, DEVICE
// - enum class Pinned: NOT_PINNED, PINNED
// - enum class Consecutive: NONE_CONSECUTIVE, CONSECUTIVE
//
// Use MemoryLocation enum instead of MappingType namespace constants

// ============================================================================
// Type Traits for Mapper Classes
// ============================================================================

/**
 * @brief Trait to check if a type implements the Mapper interface
 */
template<typename T>
struct is_mapper {
    static constexpr bool value = false;
};

template<typename T>
struct is_mapper<Mapper<T>> {
    static constexpr bool value = true;
};

template<typename T>
inline constexpr bool is_mapper_v = is_mapper<T>::value;
