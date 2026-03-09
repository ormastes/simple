/**
 * @file buffer_factory.h
 * @brief Unified buffer/queue factory interfaces (C and C++).
 *
 * Layout:
 *   1. C interface declarations (usable from plain C / FFI)
 *   2. C++ runtime helpers (only visible to C++)
 */

#pragma once

#include <cstddef>
#include <cstdint>

#include "memory/memory_types.h"
#include "forward_decls.h"

// ========================================================================
// C Interface (front section)
// ========================================================================

struct BufferFactoryHandle;

#ifndef __cplusplus
typedef struct BufferFactoryHandle BufferFactory;
#endif

#ifdef __cplusplus
extern "C" {
#endif

BufferFactoryHandle* buffer_factory_create(void);
void buffer_factory_destroy(BufferFactoryHandle* factory);

void* buffer_factory_alloc(BufferFactoryHandle* factory, MemoryType mem_type, size_t size);
void buffer_factory_dealloc(BufferFactoryHandle* factory, MemoryType mem_type, void* ptr, size_t size);

HostPool* buffer_factory_create_pool(BufferFactoryHandle* factory, MemoryType mem_type, size_t buf_size, uint16_t count);
void buffer_factory_destroy_pool(BufferFactoryHandle* factory, MemoryType mem_type, HostPool* pool);

int buffer_factory_setup_queue(BufferFactoryHandle* factory,
                               MemoryType mem_type,
                               NvmeDevice* nvme_dev,
                               NvmeQueueStruct* out_queue,
                               const char* nvme_bdf);

NvmeQueueStruct* buffer_factory_alloc_submission_queue(BufferFactoryHandle* factory, MemoryLocation mem_loc, uint16_t depth);
NvmeQueueStruct* buffer_factory_alloc_completion_queue(BufferFactoryHandle* factory, MemoryLocation mem_loc, uint16_t depth);
void buffer_factory_dealloc_submission_queue(BufferFactoryHandle* factory, NvmeQueueStruct* sq);
void buffer_factory_dealloc_completion_queue(BufferFactoryHandle* factory, NvmeQueueStruct* cq);

int buffer_factory_is_supported(const BufferFactoryHandle* factory, MemoryType mem_type);
MemoryType buffer_factory_get_recommended_kind(const BufferFactoryHandle* factory, int prefer_gpu);

BufferFactoryHandle* get_global_buffer_factory(void);

#ifdef __cplusplus
}
#endif

// ========================================================================
// C++ Runtime Factory (rear section)
// ========================================================================

#ifdef __cplusplus

class BufferFactory {
public:

    NvmeQueueStruct* alloc_submission_queue(MemoryLocation mem_loc, uint16_t depth);
    NvmeQueueStruct* alloc_completion_queue(MemoryLocation mem_loc, uint16_t depth);
    void dealloc_submission_queue(NvmeQueueStruct* sq);
    void dealloc_completion_queue(NvmeQueueStruct* cq);

    void* alloc(MemoryType mem_type, size_t size);
    void dealloc(MemoryType mem_type, void* ptr, size_t size);

    HostPool* create_pool(MemoryType mem_type, size_t buf_size, uint16_t count);
    void destroy_pool(MemoryType mem_type, HostPool* pool);
    int setup_queue(MemoryType mem_type, NvmeDevice* nvme_dev, NvmeQueueStruct* out_queue, const char* nvme_bdf);

    bool is_supported(MemoryType mem_type) const;
    MemoryType get_recommended_kind(bool prefer_gpu = false) const;
};

BufferFactory& get_buffer_factory();

#endif  // __cplusplus
