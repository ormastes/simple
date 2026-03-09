/**
 * @file cuda_io_gpu_mem.cpp
 * @brief CUDA kernel implementation for cuda_io_gpu_mem
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

#include <cstdint>
#include <cstddef>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cerrno>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <cuda_runtime_api.h>
#include <cuda.h>
#include "io/cuda_io_gpu_mem.h"
#include "io/cuda_io_gpu_mem_impl.h"  // Internal helper functions
#include "../../host/mapper/mapper_host.h"  // For Queue, NvmeCmd structures
#include "../mapper/gpu_p2p_ioctl.h"  // For GPU_P2P_MAP ioctl
#include "../../driver/gpu_p2p_nvidia/nvidia_ioctl.h"  // For GPU_P2P_NV_GET_PAGES ioctl
#include "cuda_utils.h"

namespace {
constexpr size_t kPage = 4096;

/// Calculate number of pages needed for a byte count
inline size_t bytes_to_pages(size_t bytes) {
  return (bytes + kPage - 1) / kPage;
}

/// Round up size to alignment boundary
inline size_t round_up(size_t n, size_t a) {
    return (n + (a - 1)) & ~(a - 1);
}
} // namespace

// GPU buffer pool (Module 55.0 custom implementation)
// Note: We define CudaGpuBufferPoolImpl as the concrete implementation
// The public API uses GpuBufferPool* which is an opaque pointer
struct CudaGpuBufferPoolImpl {
    NvmeDevice* dev{};              ///< Associated NVMe device
    size_t buf_size{};         ///< Size of each buffer (page-aligned)
    uint16_t cap{};            ///< Total buffer capacity
    uint16_t head{};           ///< Next buffer to acquire
    uint16_t tail{};           ///< Next buffer to release
    uint16_t in_use{};         ///< Number of buffers currently in use
    std::vector<DmaBuf> bufs;       ///< Pre-allocated GPU buffers (unified DmaBuf)
};

// ============================================================================
// Internal PRP Building Functions (C++ linkage - not exported via extern "C")
// ============================================================================

/// Build NVMe PRP (Physical Region Page) list for GPU memory segments
///
/// This function constructs PRP entries for potentially discontiguous GPU memory
/// segments. GPUDirect requires physical addresses, so segments must already
/// be mapped to device-visible IOVAs (typically via kernel module).
///
/// NVMe PRP structure:
///  - PRP1: Always points to first page
///  - PRP2: For 2-page transfers, points to second page directly
///          For >2 pages, points to a PRP list containing remaining page addresses
///
/// @param segs Array of IOVA segments (must be page-aligned)
/// @param nsegs Number of segments
/// @param[out] prp1 First page IOVA address
/// @param[out] prp2 Second page IOVA or PRP list pointer
/// @param[out] prp_list Array to store PRP list entries (pages 2..N)
/// @param prp_list_cap Capacity of prp_list array
/// @return Total transfer size in bytes, or 0 on error
size_t build_prps_for_gpu(const IovaSeg* segs, size_t nsegs,
                               uint64_t* prp1,
                               uint64_t* prp2,
                               uint64_t* prp_list,
                               size_t    prp_list_cap)
{
  // Validate inputs
  if (!segs || !nsegs || !prp1 || !prp2) return 0;

  // PRP1 always points to first page of first segment
  // Assumption: First segment is page-aligned
  *prp1 = segs[0].iova;

  // Calculate total page count across all segments
  size_t total_pages = 0;
  for (size_t seg_idx = 0; seg_idx < nsegs; seg_idx++) {
    total_pages += bytes_to_pages(segs[seg_idx].bytes);
  }

  // Handle single-page case: PRP2 = 0
  if (total_pages == 1) {
    *prp2 = 0;
    return segs[0].bytes;
  }

  // Handle two-page case: PRP2 points directly to second page
  if (total_pages == 2) {
    *prp2 = segs[0].iova + kPage;
    return 2 * kPage;
  }

  // Multi-page case: Build PRP list for pages 2..N
  // PRP list needs (total_pages - 1) entries since PRP1 covers first page
  const size_t prp_list_needed = total_pages - 1;
  if (!prp_list || prp_list_cap < prp_list_needed) {
    return 0;  // Insufficient PRP list capacity
  }

  size_t prp_idx = 0;

  // Add remaining pages from first segment (skip first page, already in PRP1)
  const size_t seg0_pages = bytes_to_pages(segs[0].bytes);
  uint64_t current_iova = segs[0].iova + kPage;  // Start at second page
  size_t remaining_pages = seg0_pages - 1;  // -1 because first page is in PRP1

  for (size_t page = 0; page < remaining_pages; page++) {
    prp_list[prp_idx++] = current_iova;
    current_iova += kPage;
  }

  // Add pages from remaining segments
  for (size_t seg_idx = 1; seg_idx < nsegs; seg_idx++) {
    current_iova = segs[seg_idx].iova;
    const size_t seg_pages = bytes_to_pages(segs[seg_idx].bytes);

    for (size_t page = 0; page < seg_pages; page++) {
      prp_list[prp_idx++] = current_iova;
      current_iova += kPage;
    }
  }

  // PRP2 points to the PRP list
  // WARNING: This uses host pointer - use build_prps_for_gpu_ex() with IOVA for real hardware
  *prp2 = (uint64_t)(prp_list);

  return total_pages * kPage;
}

/// Enhanced version that properly handles PRP list IOVA mapping for real hardware
size_t build_prps_for_gpu_ex(const IovaSeg* segs, size_t nsegs,
                                  uint64_t* prp1,
                                  uint64_t* prp2,
                                  uint64_t* prp_list,
                                  size_t    prp_list_cap,
                                  uint64_t  prp_list_iova)
{
  // Validate inputs
  if (!segs || !nsegs || !prp1 || !prp2) return 0;

  // PRP1 always points to first page of first segment
  *prp1 = segs[0].iova;

  // Calculate total page count across all segments
  size_t total_pages = 0;
  for (size_t seg_idx = 0; seg_idx < nsegs; seg_idx++) {
    total_pages += bytes_to_pages(segs[seg_idx].bytes);
  }

  // Handle single-page case: PRP2 = 0
  if (total_pages == 1) {
    *prp2 = 0;
    return segs[0].bytes;
  }

  // Handle two-page case: PRP2 points directly to second page
  if (total_pages == 2) {
    *prp2 = segs[0].iova + kPage;
    return 2 * kPage;
  }

  // Multi-page case: Build PRP list for pages 2..N
  const size_t prp_list_needed = total_pages - 1;
  if (!prp_list || prp_list_cap < prp_list_needed) {
    return 0;  // Insufficient PRP list capacity
  }

  size_t prp_idx = 0;

  // Add remaining pages from first segment (skip first page, already in PRP1)
  const size_t seg0_pages = bytes_to_pages(segs[0].bytes);
  uint64_t current_iova = segs[0].iova + kPage;  // Start at second page
  size_t remaining_pages = seg0_pages - 1;

  for (size_t page = 0; page < remaining_pages; page++) {
    prp_list[prp_idx++] = current_iova;
    current_iova += kPage;
  }

  // Add pages from remaining segments
  for (size_t seg_idx = 1; seg_idx < nsegs; seg_idx++) {
    current_iova = segs[seg_idx].iova;
    const size_t seg_pages = bytes_to_pages(segs[seg_idx].bytes);

    for (size_t page = 0; page < seg_pages; page++) {
      prp_list[prp_idx++] = current_iova;
      current_iova += kPage;
    }
  }

  // PRP2 points to the PRP list IOVA (for real hardware) or host pointer (for testing)
  if (prp_list_iova != 0) {
    *prp2 = prp_list_iova;  // Use provided IOVA for real hardware
  } else {
    *prp2 = (uint64_t)(prp_list);  // Fallback to host pointer for testing
  }

  return total_pages * kPage;
}

// ============================================================================
// Public C API Functions (exported via extern "C")
// ============================================================================

extern "C" {

// ============================================================================
// Runtime GPU Submit API with Template Support
// ============================================================================

/// Submit NVMe command with pre-built PRPs (runtime dispatch version)
/// Unified function that handles both READ/WRITE and all doorbell modes
__host__ uint16_t cuda_submit_runtime(CommandType cmd, DoorbellType doorbell,
                                           Queue* iosq, uint32_t nsid,
                                           uint64_t slba, uint32_t lba_size,
                                           size_t bytes,
                                           uint64_t prp1, uint64_t prp2)
{
    if (!iosq || !iosq->db || !iosq->vaddr) return NVME_CID_ERROR;
    if (!lba_size || !bytes || (bytes % lba_size)) return NVME_CID_ERROR;

    // Check queue full
    const uint16_t next_tail = (uint16_t)((iosq->tail + 1) % iosq->entries);
    if (next_tail == iosq->head) return NVME_CID_QUEUE_FULL;

    // Calculate number of logical blocks (NLB field is 0-based)
    const uint16_t nlb0 = (uint16_t)((bytes / lba_size) - 1);

    // Build NVMe command
    NvmeCmd nvme_cmd;
    std::memset(&nvme_cmd, 0, sizeof(nvme_cmd));
    nvme_cmd.opc = (cmd == CMD_READ) ? OPC_NVM_READ : OPC_NVM_WRITE;
    nvme_cmd.cid = iosq->tail;
    nvme_cmd.nsid = nsid;
    nvme_cmd.prp1 = prp1;
    nvme_cmd.prp2 = prp2;
    nvme_cmd.cdw10 = (uint32_t)(slba & 0xFFFFFFFFu);
    nvme_cmd.cdw11 = (uint32_t)(slba >> 32);
    nvme_cmd.cdw12 = nlb0;

    // Copy command to queue entry
    NvmeCmd* entry = (NvmeCmd*)((uint8_t*)iosq->vaddr +
                                (size_t)iosq->tail * iosq->entry_size);
    std::memcpy(entry, &nvme_cmd, sizeof(nvme_cmd));

    // Save CID before advancing tail
    uint16_t cid = iosq->tail;

    // Advance tail
    iosq->tail = next_tail;

    // Ring doorbell based on mode
    switch (doorbell) {
        case DOORBELL_MMIO:
            // Immediate doorbell ring via MMIO
            *iosq->db = iosq->tail;
            break;

        case DOORBELL_DEFERRED:
            // Deferred doorbell (caller will ring later or use shadow doorbell)
            // No action needed here
            break;

        case DOORBELL_DEFERRED_EVENTIDX:
            // Deferred with event index optimization (not implemented; relies on phase bit polling)
            // For now, treat same as DEFERRED
            break;
    }

    return cid;
}

// ============================================================================
// GPU Buffer Pool Implementation
// ============================================================================

/// Create pre-allocated pool of GPU device memory buffers
/// NOTE: This is a STUB implementation since actual GPU P2P mapping requires kernel module
/// In real implementation, would need to:
///   1. Allocate GPU memory with cudaMalloc
///   2. Get physical addresses via kernel module ioctl
///   3. Map GPU physical pages to NVMe-visible IOVAs
///   4. Build PRP lists for each buffer
__host__ CudaGpuPool* cuda_gpu_pool_create(NvmeDevice* d, size_t buf_size, uint16_t count) {
    if (!d || buf_size == 0 || count == 0) return nullptr;

    const size_t page_size = nvme_get_page_size(d);
    const ItemSize item_size = nvme_get_item_size(d);
    const size_t actual_buf_size = item_size.total_size;

    auto* p = new CudaGpuBufferPoolImpl();
    p->dev = d;
    p->buf_size = round_up(actual_buf_size, page_size);
    p->cap = count;
    p->bufs.resize(count);

    const size_t pages = p->buf_size / page_size;

    // NVMe PRP limit check
    const size_t kMaxPRPPages = (page_size / 8) * 2 + 1;
    if (pages > kMaxPRPPages) {
        std::fprintf(stderr,
            "ERROR: cuda_gpu_pool_create() - Buffer size %zu bytes (%zu pages) exceeds NVMe PRP limit.\n"
            "  Maximum: %zu pages\n",
            p->buf_size, pages, kMaxPRPPages);
        delete p;
        return nullptr;
    }

    // Use extracted buffer construction logic for GPU device memory
    if (nvme_buffer_impl::fill_pool_buffers(p->bufs, d, item_size, count, MemoryType::PINNED_DEVICE) != 0) {
        std::fprintf(stderr, "ERROR: cuda_gpu_pool_create() - Failed to construct GPU buffers\n");
        delete p;
        return nullptr;
    }

    // Try to map GPU buffers via P2P kernel module (nvidia_ioctl.h interface)
    int p2p_fd = open("/dev/gpu_p2p_nvidia", O_RDWR);
    if (p2p_fd >= 0) {
        bool all_mapped = true;
        for (auto& buf : p->bufs) {
            if (!buf.addr) continue;

            buf.using_p2p = false;
            // Get P2P tokens for this GPU buffer (optional - persistent API works with token=0)
            CUDA_POINTER_ATTRIBUTE_P2P_TOKENS tokens{};
            CUresult res = cuPointerGetAttribute(&tokens, CU_POINTER_ATTRIBUTE_P2P_TOKENS,
                                                  (CUdeviceptr)buf.addr);
            if (res != CUDA_SUCCESS) {
                std::fprintf(stderr, "WARNING: Could not query P2P tokens for buffer %p (using persistent API)\n", buf.addr);
                tokens.p2pToken = 0;
                tokens.vaSpaceToken = 0;
            } else if (tokens.p2pToken == 0) {
                std::fprintf(stderr, "INFO: P2P token is 0 for buffer %p (will use persistent API)\n", buf.addr);
            }

            // Allocate page info array for kernel to fill
            constexpr size_t kMaxPages = 64;  // 64 * 64KB = 4MB max
            std::vector<nv_page_info> pages(kMaxPages);

            // Call NVIDIA bridge kernel module using correct ioctl interface
            // When p2p_token=0, kernel driver uses nvidia_p2p_get_pages_persistent()
            struct nv_get_pages_req req{};
            req.gpu_va = (uint64_t)buf.addr;
            req.bytes = buf.bytes;
            req.p2p_token = tokens.p2pToken;
            req.va_space = tokens.vaSpaceToken;
            req.flags = 0;
            req.pages_user_ptr = (uint64_t)pages.data();

            if (ioctl(p2p_fd, GPU_P2P_NV_GET_PAGES, &req) == 0 && req.num_pages > 0) {
                // Use first page's physical address as PRP1
                buf.prp1 = pages[0].phys_addr;
                buf.prp2 = (req.num_pages > 1) ? pages[1].phys_addr : 0;
                buf.using_p2p = buf.prp1 != 0;
                std::fprintf(stderr, "INFO: GPU P2P mapped buffer %p -> phys 0x%llx (%u pages, page_size=%u)\n",
                             buf.addr, (unsigned long long)buf.prp1, req.num_pages, req.page_size);
            } else {
                std::fprintf(stderr, "WARNING: GPU_P2P_NV_GET_PAGES ioctl failed for buffer %p (errno=%d)\n", buf.addr, errno);
                all_mapped = false;
            }
        }
        close(p2p_fd);

        if (all_mapped) {
            std::fprintf(stderr, "INFO: cuda_gpu_pool_create() - All GPU buffers P2P mapped via kernel module\n");
            return reinterpret_cast<CudaGpuPool*>(p);
        }
    }

    // Fallback: buffers allocated but not P2P mapped
    std::fprintf(stderr,
        "WARNING: cuda_gpu_pool_create() - GPU P2P buffer pool created but NOT MAPPED.\n"
        "  Real P2P DMA requires kernel module for IOVA mapping.\n"
        "  See modules 55.1-55.3 for complete implementation.\n");

    return reinterpret_cast<CudaGpuPool*>(p);
}

/// Acquire buffer from GPU pool (non-blocking)
__host__ DmaBuf* cuda_gpu_pool_acquire(CudaGpuPool* pool) {
    auto* p = reinterpret_cast<CudaGpuBufferPoolImpl*>(pool);
    if (!p || p->in_use == p->cap) return nullptr;
    DmaBuf* b = &p->bufs[p->head];
    p->head = (uint16_t)((p->head + 1) % p->cap);
    p->in_use++;
    return b;
}

/// Release buffer back to GPU pool
__host__ void cuda_gpu_pool_release(CudaGpuPool* pool, DmaBuf* b) {
    auto* p = reinterpret_cast<CudaGpuBufferPoolImpl*>(pool);
    if (!p) return;
    (void)b;  // Buffer identity not checked (trust caller)
    p->tail = (uint16_t)((p->tail + 1) % p->cap);
    p->in_use--;
}

/// Destroy GPU pool and free all buffers
__host__ void cuda_gpu_pool_destroy(CudaGpuPool* pool) {
    auto* p = reinterpret_cast<CudaGpuBufferPoolImpl*>(pool);
    if (!p) return;

    // Free single pool allocation (all buffers and PRPs in one block)
    if (!p->bufs.empty()) {
        const auto& first_buf = p->bufs[0];
        if (first_buf.mem_type == MemoryType::HOST) {
            std::free(first_buf.addr);
        } else if (first_buf.mem_type == MemoryType::PINNED_HOST) {
            cudaFreeHost(first_buf.addr);
        } else {
            cuda_free(first_buf.addr);
        }
    }

    // Free IOVA segments (still separate allocations)
    for (auto& buf : p->bufs) {
        delete[] buf.segs;
    }

    delete p;
}

// ============================================================================
// GPU Pinned Consecutive Buffer Implementation (Module 55.0.3)
// ============================================================================

/// Create GPU device memory consecutive buffer with P2P DMA mapping
/// NOTE: STUB implementation - requires kernel module for real P2P mapping
__host__ Buffer* cuda_gpu_create_device_consecutive_buffer(size_t buffer_size) {
    if (buffer_size == 0) return nullptr;

    // Allocate GPU device memory
    void* device_ptr = cuda_malloc<uint8_t>(buffer_size);
    if (!device_ptr) return nullptr;

    // Create buffer descriptor (real implementation needs kernel module for IOVA)
    Buffer* b = new Buffer();
    b->addr = device_ptr;
    b->bytes = buffer_size;
    b->iova = 0;  // STUB - no IOVA mapping without kernel module
    b->mem_type = MemoryType::PINNED_DEVICE;
    b->consecutive = Consecutive::CONSECUTIVE;

    std::fprintf(stderr,
        "WARNING: cuda_gpu_create_device_consecutive_buffer() - GPU allocated but NOT MAPPED.\n"
        "  Real P2P DMA requires kernel module. See modules 55.1-55.3.\n");

    return b;
}

/// Destroy GPU device memory buffer
__host__ void cuda_gpu_buffer_destroy(Buffer* b) {
    if (!b) return;
    cuda_free(b->addr);  // In real implementation, would also unmap IOVA via kernel module
    delete b;
}

} // extern "C"
