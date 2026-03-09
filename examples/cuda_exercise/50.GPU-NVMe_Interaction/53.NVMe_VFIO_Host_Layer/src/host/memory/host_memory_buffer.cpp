/**
 * @file host_memory_buffer.cpp
 * @brief Host memory buffer pool implementation for NVMe DMA operations
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-01
 */

#include "host_memory_buffer.h"
#include "mapper/mapper.h"
#include "mapper/mapper_host_impl.h"
#include "mapper/mapper_host.h"

#include <cstdlib>
#include <cstring>
#include <cstdio>

// Forward declaration of internal NvmeDevice structure (defined in nvme_vio_host.cpp)
// We access the global device through external linkage
extern NvmeDevice* g_dev;

namespace {
constexpr size_t kPage = 4096;

/// Round up size to alignment boundary (used for consecutive buffer)
inline size_t round_up(size_t n, size_t a) {
    return (n + (a - 1)) & ~(a - 1);
}

/// Allocate page-aligned and zero-initialized memory (used for consecutive buffer)
inline void* page_alloc(size_t bytes) {
    size_t rounded = round_up(bytes, kPage);
    void* p = nullptr;
    if (posix_memalign(&p, kPage, rounded) != 0) {
        std::perror("posix_memalign");
        std::exit(1);
    }
    std::memset(p, 0, rounded);
    return p;
}
} // anonymous namespace

// ============================================================================
// Host Memory Buffer Pool Implementation
// ============================================================================

// Global singleton HostMapper instance for legacy functions
static HostMapper g_host_mapping;

HostPool* host_pool_create(NvmeDevice* d, uint16_t count, MapperInterface* mapping) {
    DEBUG_ASSERT(d != nullptr, "host_pool_create: device is null");
    DEBUG_ASSERT(count > 0, "host_pool_create: count must be positive");

    const size_t page_size = nvme_get_page_size(d);
    const ItemSize item_size = nvme_get_item_size(d);
    const size_t buf_size = item_size.total_size;

    auto* p = new HostPool();  // Use modern Pool template
    p->dev = d;
    p->buf_size = round_up(buf_size, page_size);
    p->cap = count;
    p->bufs.resize(count);
    const size_t pages = p->buf_size / page_size;

    // NVMe Spec: PRP List Limit Enforcement
    // Note: This calculation assumes page_size (varies by device and system)
    // - Maximum PRP entries per page: page_size / 8
    // - Maximum PRP list pages: 2 (spec limit)
    // - Maximum PRP entries: (page_size / 8) * 2
    // - Maximum data pages with PRPs: (page_size / 8) * 2 + 1 (prp1)
    //
    // For buffers larger than this limit, NVMe requires SGL (Scatter Gather List) instead of PRPs.
    const size_t kMaxPRPPages = (page_size / 8) * 2 + 1;  // Dynamic based on page size

    if (pages > kMaxPRPPages) {
        std::fprintf(stderr,
            "ERROR: host_pool_create() - Buffer size %zu bytes (%zu pages of %zu bytes) exceeds NVMe PRP limit.\n"
            "  Requested: %zu pages (%zu MB)\n"
            "  Maximum:   %zu pages (%zu MB)\n"
            "  NVMe spec limits PRP lists to 2 pages (page_size/8 * 2 entries).\n"
            "  For larger buffers, use SGL (Scatter Gather List) instead.\n"
            "  Hint: Split large transfers into multiple smaller chunks.\n",
            p->buf_size, pages, page_size,
            pages, pages * page_size / (1024 * 1024),
            kMaxPRPPages, kMaxPRPPages * page_size / (1024 * 1024));
        delete p;
        return nullptr;
    }

    // Use provided mapping or default to global instance
    if (!mapping) {
        mapping = &g_host_mapping;
    }

    // Use extracted buffer construction logic with ItemSize
    if (nvme_buffer_impl::fill_pool_buffers(p->bufs, d, item_size, count, MemoryType::HOST, mapping) != 0) {
        std::fprintf(stderr, "ERROR: host_pool_create() - Failed to construct buffers\n");
        delete p;
        return nullptr;
    }

    // Set pool tracking fields for proper cleanup
    // fill_pool_buffers() allocates ONE contiguous block, bufs[0].addr is the base
    p->mapper = mapping;
    p->pool_iova = p->bufs[0].iova;  // Base IOVA of pool allocation

    // Calculate total allocation size: (buffer + PRP list) * count
    const size_t prplist_bytes = p->bufs[0].prplist_bytes;
    const size_t chunk_size = p->buf_size + prplist_bytes;
    p->total_size = chunk_size * count;

    // Verify pool properties (postconditions)
    DEBUG_ASSERT(p != nullptr, "host_pool_create: created pool is null");
    DEBUG_ASSERT(p->bufs[0].addr != nullptr, "host_pool_create: pool buffer has null address");
    DEBUG_ASSERT(p->cap == count, "host_pool_create: capacity mismatch");
    DEBUG_ASSERT(p->in_use == 0, "host_pool_create: new pool should have in_use=0");
    DEBUG_ASSERT(p->buf_size > 0, "host_pool_create: buffer size is zero");

    return p;
}

DmaBuf* host_pool_acquire(HostPool* p) {
    DEBUG_ASSERT(p != nullptr, "host_pool_acquire: pool is null");
    DmaBuf* buf = p->acquire();

    // Verify buffer properties when non-null (null is valid when pool is full)
    if (buf != nullptr) {
        DEBUG_ASSERT(buf->addr != nullptr, "host_pool_acquire: buffer has null address");
        DEBUG_ASSERT(buf->bytes > 0, "host_pool_acquire: buffer has zero size");
        DEBUG_ASSERT(buf->iova != 0, "host_pool_acquire: buffer has zero IOVA");
    }

    return buf;
}

void host_pool_release(HostPool* p, DmaBuf* b) {
    p->release(b);
}

void host_pool_destroy(HostPool* p, MapperInterface* mapping) {
    if (!p) return;

    // Pool memory was allocated in ONE contiguous block by fill_pool_buffers()
    // bufs[0].addr points to the base of this allocation
    // Pool destructor handles unmapping via p->mapper, p->total_size, p->pool_iova

    // Free the pool memory ONCE (not individual buffers!)
    if (!p->bufs.empty() && p->bufs[0].addr) {
        std::free(p->bufs[0].addr);  // Free the entire pool allocation
    }

    delete p;  // Pool destructor will unmap IOVA
}

// ============================================================================
// Host Consecutive Buffer Implementation
// ============================================================================

Buffer* host_create_consecutive_buffer(size_t buffer_size, MapperInterface* mapping) {
    // Use provided mapping or default to global instance
    if (!mapping) {
        mapping = &g_host_mapping;
    }

    const size_t page_size = nvme_get_page_size(nullptr);  // Uses global device
    size_t aligned_size = round_up(buffer_size, page_size);
    void* host = page_alloc(aligned_size);
    uint64_t iova = 0;

    if (mapping->map_memory_runtime(g_dev, host, aligned_size, &iova) != 0) {
        std::fprintf(stderr, "ERROR: host_create_consecutive_buffer() - Failed to map buffer to IOVA\n");
        std::free(host);
        return nullptr;
    }

    Buffer* b = new Buffer();
    b->addr = host;
    b->bytes = aligned_size;
    b->iova = iova;
    b->mem_type = MemoryType::HOST;
    b->consecutive = Consecutive::CONSECUTIVE;
    return b;
}

void host_buffer_destroy(Buffer* b, MapperInterface* mapping) {
    if (!b) return;

    // Use provided mapping or default to global instance
    if (!mapping) {
        mapping = &g_host_mapping;
    }

    if (b->addr && b->iova) {
        mapping->unmap_memory_runtime(g_dev, b->addr, b->bytes, b->iova);
    }
    if (b->addr) {
        std::free(b->addr);
    }
    delete b;
}
