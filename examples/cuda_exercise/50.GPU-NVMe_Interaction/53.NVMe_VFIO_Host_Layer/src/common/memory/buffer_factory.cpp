/**
 * @file buffer_factory.cpp
 * @brief Implementation of the runtime buffer/queue factory.
 */

#include "memory/buffer_factory.h"

#include "doorbell/nvme_doorbell.h"
#include "memory/host_memory_buffer.h"
#include "memory/memory_pool.h"
#include "queue/nvme_queue.h"
#include "cuda_utils.h"

#include <cstring>
#include <new>
#include <stdexcept>

namespace {

constexpr size_t kSqEntrySize = 64;
constexpr size_t kCqEntrySize = 16;

struct HostAllocator {
    static void* alloc(size_t size) {
        if (size == 0) {
            return nullptr;
        }
        void* ptr = nullptr;
        if (posix_memalign(&ptr, 4096, size) != 0) {
            return nullptr;
        }
        std::memset(ptr, 0, size);
        return ptr;
    }

    static void dealloc(void* ptr, size_t) {
        std::free(ptr);
    }
};

struct CudaHostAllocator {
    static void* alloc(size_t size) {
        if (size == 0) return nullptr;
        void* ptr = nullptr;
        CHECK_CUDA_MSG(cudaHostAlloc(&ptr, size, cudaHostAllocPortable), "CudaHostAllocator::alloc");
        std::memset(ptr, 0, size);
        return ptr;
    }

    static void dealloc(void* ptr, size_t) {
        if (ptr) CHECK_CUDA_MSG(cudaFreeHost(ptr), "CudaHostAllocator::dealloc");
    }
};

struct CudaGpuAllocator {
    static void* alloc(size_t size) {
        return cuda_calloc<uint8_t>(size);  // Allocate and zero-initialize
    }

    static void dealloc(void* ptr, size_t) {
        cuda_free(ptr);
    }
};

MemoryType queue_mem_from_location(MemoryLocation loc) {
    return (loc == MemoryLocation::HOST) ? MemoryType::PINNED_HOST : MemoryType::PINNED_DEVICE;
}

void init_queue_common(NvmeQueueStruct* q, uint16_t depth) {
    q->sq_depth = (q->sq_base != nullptr) ? depth : 0;
    q->cq_depth = (q->cq_base != nullptr) ? depth : 0;
    q->qid = 0;
    q->nsid = 1;
    q->page_size = 4096;
    q->sq_phase = 1;
    q->cq_phase = 1;
    q->doorbell_mode = DOORBELL_MODE_HOST_MMIO;
    q->sq_tail = 0;
    q->cq_head = 0;
    q->read_cmd_pool = nullptr;
    q->write_cmd_pool = nullptr;
}

}  // namespace

// ============================================================================
// Queue helpers
// ============================================================================

NvmeQueueStruct* BufferFactory::alloc_submission_queue(MemoryLocation mem_loc, uint16_t depth) {
    if (depth == 0) {
        return nullptr;
    }

    auto* sq = new (std::nothrow) NvmeQueueStruct{};
    if (!sq) {
        return nullptr;
    }

    const size_t bytes = depth * kSqEntrySize;
    const MemoryType mem_type = queue_mem_from_location(mem_loc);

    void* queue_mem = alloc(mem_type, bytes);
    if (!queue_mem) {
        delete sq;
        return nullptr;
    }

    std::memset(sq, 0, sizeof(*sq));
    sq->sq_base = static_cast<NvmeCmd*>(queue_mem);
    init_queue_common(sq, depth);
    return sq;
}

NvmeQueueStruct* BufferFactory::alloc_completion_queue(MemoryLocation mem_loc, uint16_t depth) {
    if (depth == 0) {
        return nullptr;
    }

    auto* cq = new (std::nothrow) NvmeQueueStruct{};
    if (!cq) {
        return nullptr;
    }

    const size_t bytes = depth * kCqEntrySize;
    const MemoryType mem_type = queue_mem_from_location(mem_loc);

    void* queue_mem = alloc(mem_type, bytes);
    if (!queue_mem) {
        delete cq;
        return nullptr;
    }

    std::memset(cq, 0, sizeof(*cq));
    cq->cq_base = static_cast<NvmeCqe*>(queue_mem);
    init_queue_common(cq, depth);
    return cq;
}

void BufferFactory::dealloc_submission_queue(NvmeQueueStruct* sq) {
    if (!sq) {
        return;
    }

    if (sq->sq_base) {
        const size_t bytes = sq->sq_depth * kSqEntrySize;
        dealloc(MemoryType::PINNED_HOST, sq->sq_base, bytes);
    }
    delete sq;
}

void BufferFactory::dealloc_completion_queue(NvmeQueueStruct* cq) {
    if (!cq) {
        return;
    }

    if (cq->cq_base) {
        const size_t bytes = cq->cq_depth * kCqEntrySize;
        dealloc(MemoryType::PINNED_HOST, cq->cq_base, bytes);
    }
    delete cq;
}

// ============================================================================
// Allocation helpers
// ============================================================================

void* BufferFactory::alloc(MemoryType mem_type, size_t size) {
    switch (mem_type) {
    case MemoryType::HOST:
        return HostAllocator::alloc(size);
    case MemoryType::PINNED_HOST:
        return CudaHostAllocator::alloc(size);
    case MemoryType::PINNED_DEVICE:
        return CudaGpuAllocator::alloc(size);
    default:
        throw std::invalid_argument("Unknown MemoryType in BufferFactory::alloc");
    }
}

void BufferFactory::dealloc(MemoryType mem_type, void* ptr, size_t size) {
    if (!ptr) {
        return;
    }

    switch (mem_type) {
    case MemoryType::HOST:
        HostAllocator::dealloc(ptr, size);
        break;
    case MemoryType::PINNED_HOST:
        CudaHostAllocator::dealloc(ptr, size);
        break;
    case MemoryType::PINNED_DEVICE:
        CudaGpuAllocator::dealloc(ptr, size);
        break;
    default:
        throw std::invalid_argument("Unknown MemoryType in BufferFactory::dealloc");
    }
}

HostPool* BufferFactory::create_pool(MemoryType mem_type, size_t buf_size, uint16_t count) {
    if (mem_type != MemoryType::HOST && mem_type != MemoryType::PINNED_HOST) {
        throw std::runtime_error("Only host pools are supported in Module 53");
    }

    auto* pool = new HostPool();
    pool->buf_size = buf_size;
    pool->cap = count;
    pool->bufs.resize(count);
    return pool;
}

void BufferFactory::destroy_pool(MemoryType mem_type, HostPool* pool) {
    if (!pool) {
        return;
    }
    if (mem_type != MemoryType::HOST && mem_type != MemoryType::PINNED_HOST) {
        throw std::runtime_error("Only host pools are supported in Module 53");
    }
    delete pool;
}

int BufferFactory::setup_queue(MemoryType mem_type,
                               NvmeDevice* nvme_dev,
                               NvmeQueueStruct* out_queue,
                               const char* nvme_bdf) {
    (void)nvme_dev;
    (void)out_queue;
    (void)nvme_bdf;
    if (mem_type == MemoryType::HOST || mem_type == MemoryType::PINNED_HOST) {
        return 0;
    }
    return -1;
}

bool BufferFactory::is_supported(MemoryType mem_type) const {
    switch (mem_type) {
    case MemoryType::HOST:
    case MemoryType::PINNED_HOST:
        return true;
    case MemoryType::PINNED_DEVICE:
        return false;  // Reserved for Module 55+
    default:
        return false;
    }
}

MemoryType BufferFactory::get_recommended_kind(bool prefer_gpu) const {
    if (prefer_gpu) {
        return MemoryType::PINNED_DEVICE;
    }
    return MemoryType::PINNED_HOST;
}

BufferFactory& get_buffer_factory() {
    static BufferFactory factory;
    return factory;
}

// ============================================================================
// C interface
// ============================================================================

extern "C" {

BufferFactoryHandle* buffer_factory_create(void) {
    try {
        return reinterpret_cast<BufferFactoryHandle*>(new BufferFactory());
    } catch (...) {
        return nullptr;
    }
}

void buffer_factory_destroy(BufferFactoryHandle* factory) {
    delete reinterpret_cast<BufferFactory*>(factory);
}

void* buffer_factory_alloc(BufferFactoryHandle* factory, MemoryType mem_type, size_t size) {
    if (!factory) {
        return nullptr;
    }
    try {
        return reinterpret_cast<BufferFactory*>(factory)->alloc(mem_type, size);
    } catch (...) {
        return nullptr;
    }
}

void buffer_factory_dealloc(BufferFactoryHandle* factory, MemoryType mem_type, void* ptr, size_t size) {
    if (!factory) {
        return;
    }
    try {
        reinterpret_cast<BufferFactory*>(factory)->dealloc(mem_type, ptr, size);
    } catch (...) {
    }
}

HostPool* buffer_factory_create_pool(BufferFactoryHandle* factory, MemoryType mem_type, size_t buf_size, uint16_t count) {
    if (!factory) {
        return nullptr;
    }
    try {
        return reinterpret_cast<BufferFactory*>(factory)->create_pool(mem_type, buf_size, count);
    } catch (...) {
        return nullptr;
    }
}

void buffer_factory_destroy_pool(BufferFactoryHandle* factory, MemoryType mem_type, HostPool* pool) {
    if (!factory || !pool) {
        return;
    }
    try {
        reinterpret_cast<BufferFactory*>(factory)->destroy_pool(mem_type, pool);
    } catch (...) {
    }
}

int buffer_factory_setup_queue(BufferFactoryHandle* factory,
                               MemoryType mem_type,
                               NvmeDevice* nvme_dev,
                               NvmeQueueStruct* out_queue,
                               const char* nvme_bdf) {
    if (!factory) {
        return -1;
    }
    try {
        return reinterpret_cast<BufferFactory*>(factory)->setup_queue(mem_type, nvme_dev, out_queue, nvme_bdf);
    } catch (...) {
        return -1;
    }
}

NvmeQueueStruct* buffer_factory_alloc_submission_queue(BufferFactoryHandle* factory, MemoryLocation mem_loc, uint16_t depth) {
    if (!factory) {
        return nullptr;
    }
    try {
        return reinterpret_cast<BufferFactory*>(factory)->alloc_submission_queue(mem_loc, depth);
    } catch (...) {
        return nullptr;
    }
}

NvmeQueueStruct* buffer_factory_alloc_completion_queue(BufferFactoryHandle* factory, MemoryLocation mem_loc, uint16_t depth) {
    if (!factory) {
        return nullptr;
    }
    try {
        return reinterpret_cast<BufferFactory*>(factory)->alloc_completion_queue(mem_loc, depth);
    } catch (...) {
        return nullptr;
    }
}

void buffer_factory_dealloc_submission_queue(BufferFactoryHandle* factory, NvmeQueueStruct* sq) {
    if (!factory) {
        return;
    }
    try {
        reinterpret_cast<BufferFactory*>(factory)->dealloc_submission_queue(sq);
    } catch (...) {
    }
}

void buffer_factory_dealloc_completion_queue(BufferFactoryHandle* factory, NvmeQueueStruct* cq) {
    if (!factory) {
        return;
    }
    try {
        reinterpret_cast<BufferFactory*>(factory)->dealloc_completion_queue(cq);
    } catch (...) {
    }
}

int buffer_factory_is_supported(const BufferFactoryHandle* factory, MemoryType mem_type) {
    if (!factory) {
        return 0;
    }
    try {
        return reinterpret_cast<const BufferFactory*>(factory)->is_supported(mem_type) ? 1 : 0;
    } catch (...) {
        return 0;
    }
}

MemoryType buffer_factory_get_recommended_kind(const BufferFactoryHandle* factory, int prefer_gpu) {
    if (!factory) {
        return MemoryType::HOST;
    }
    try {
        return reinterpret_cast<const BufferFactory*>(factory)->get_recommended_kind(prefer_gpu != 0);
    } catch (...) {
        return MemoryType::HOST;
    }
}

BufferFactoryHandle* get_global_buffer_factory(void) {
    return reinterpret_cast<BufferFactoryHandle*>(&get_buffer_factory());
}

}  // extern "C"
