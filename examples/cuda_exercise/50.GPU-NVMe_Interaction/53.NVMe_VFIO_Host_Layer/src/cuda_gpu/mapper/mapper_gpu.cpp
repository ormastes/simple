/**
 * @file mapper_gpu.cpp
 * @brief CUDA implementation for GPU-side NVMe memory mapper operations
 *
 * Includes:
 * - GPU buffer allocation and management
 * - CUDA P2P token queries
 * - GPU queue setup for NVMe submission (merged from nvme_gpu_submit_setup.cpp 2025-11-01)
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// SPDX-License-Identifier: MIT OR GPL-2.0
#include <cstdint>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <unistd.h>
#include <dlfcn.h>
#include <cstdlib>
#include <sys/ioctl.h>
#include <cuda_runtime_api.h>
#include <cuda.h>

#include "mapper/mapper_gpu.h"
#include "../../host/mapper/mapper_host.h"
#include "mapper/gpu_p2p_ioctl.h"
#include "doorbell/nvme_doorbell.h"
#include "cuda_utils.h"

// External functions for IOVA mapping (from host layer)
extern "C" {
    int host_map_iova(void* host, size_t bytes, uint64_t* out_iova);
    int host_unmap_iova(void* host, size_t bytes, uint64_t iova);
}

// ============================================================================
// GPU Buffer Management
// ============================================================================

extern "C" Buffer* nvme_gpu_create_cuda_pinned_consecutive_buffer(size_t buffer_size){
  if (!buffer_size) return nullptr;

  // Initialize CUDA Driver API (required for cuMemAlloc)
  CUresult res = cuInit(0);
  if (res != CUDA_SUCCESS) {
    fprintf(stderr, "ERROR: cuInit failed: %d\n", res);
    return nullptr;
  }

  // Get current context
  CUcontext ctx;
  res = cuCtxGetCurrent(&ctx);
  if (res != CUDA_SUCCESS || !ctx) {
    // No context, create one
    CUdevice dev;
    cuDeviceGet(&dev, 0);
    CUctxCreateParams params = {};
    params.execAffinityParams = nullptr;
    res = cuCtxCreate(&ctx, &params, 0, dev);
    if (res != CUDA_SUCCESS) {
      fprintf(stderr, "ERROR: cuCtxCreate failed: %d\n", res);
      return nullptr;
    }
  }

  // Use CUDA Driver API with CU_MEM_CREATE_USAGE_TILE_POOL flag for P2P
  // Try regular cuMemAlloc first
  CUdeviceptr dptr = 0;
  res = cuMemAlloc(&dptr, buffer_size);
  if (res != CUDA_SUCCESS) {
    const char* err_str = nullptr;
    cuGetErrorString(res, &err_str);
    fprintf(stderr, "ERROR: cuMemAlloc failed: %d (%s)\n", res, err_str ? err_str : "unknown");
    return nullptr;
  }

  fprintf(stderr, "INFO: Allocated GPU buffer with cuMemAlloc: ptr=%p, size=%zu\n",
          (void*)dptr, buffer_size);

  // Check if we can get P2P tokens
  CUDA_POINTER_ATTRIBUTE_P2P_TOKENS test_tokens{};
  res = cuPointerGetAttribute(&test_tokens, CU_POINTER_ATTRIBUTE_P2P_TOKENS, dptr);
  bool p2p_available = false;
  if (res == CUDA_SUCCESS) {
    fprintf(stderr, "INFO: P2P tokens available: p2p_token=0x%llx, va_space=0x%x\n",
            (unsigned long long)test_tokens.p2pToken, test_tokens.vaSpaceToken);
    if (test_tokens.p2pToken == 0) {
      fprintf(stderr, "WARNING: P2P token is 0 - GPU P2P may not be supported\n");
      fprintf(stderr, "         Falling back to pinned host memory for NVMe DMA\n");
    } else {
      p2p_available = true;
    }
  } else {
    fprintf(stderr, "WARNING: Could not query P2P tokens: %d\n", res);
    fprintf(stderr, "         Falling back to pinned host memory for NVMe DMA\n");
  }

  // If P2P is not available, fall back to pinned host memory
  if (!p2p_available) {
    // Free GPU memory
    cuMemFree(dptr);

    // Allocate pinned host memory instead
    void* host_ptr = nullptr;
    cudaError_t cuda_err = cudaHostAlloc(&host_ptr, buffer_size, cudaHostAllocPortable);
    if (cuda_err != cudaSuccess) {
      fprintf(stderr, "ERROR: cudaHostAlloc fallback failed: %s\n", cudaGetErrorString(cuda_err));
      return nullptr;
    }

    // Map to IOVA for NVMe DMA
    uint64_t iova = 0;
    if (host_map_iova(host_ptr, buffer_size, &iova) != 0) {
      fprintf(stderr, "ERROR: Failed to map pinned host memory to IOVA\n");
      cudaFreeHost(host_ptr);
      return nullptr;
    }

    fprintf(stderr, "INFO: Using pinned host memory fallback: ptr=%p, iova=0x%llx\n",
            host_ptr, (unsigned long long)iova);

    Buffer* b = new Buffer();
    b->addr = host_ptr;
    b->bytes = buffer_size;
    b->iova = iova;
    b->mem_type = MemoryType::PINNED_HOST;  // Mark as pinned host
    b->consecutive = Consecutive::CONSECUTIVE;
    return b;
  }

  // P2P is available - try to map GPU memory via kernel module
  Buffer* b = new Buffer();
  b->addr = (void*)dptr;
  b->bytes = buffer_size;
  b->iova = 0;
  b->mem_type = MemoryType::PINNED_DEVICE;
  b->consecutive = Consecutive::CONSECUTIVE;

  // Try to open P2P kernel module device
  int p2p_fd = open("/dev/gpu_p2p_nvme", O_RDWR);
  if (p2p_fd >= 0) {
    // Kernel module is available - try GPU_P2P_MAP ioctl
    struct gpu_p2p_req req{};
    req.gpu_va = (uint64_t)dptr;
    req.bytes = buffer_size;
    req.nvme_pci_bdf = 0;  // Will be set by caller
    req.p2p_token = test_tokens.p2pToken;
    req.va_space = test_tokens.vaSpaceToken;
    req.max_segs = 1;
    req.flags = 0;

    // Allocate output buffer for segments
    struct gpu_p2p_seg seg{};
    req.out_user_ptr = (uint64_t)&seg;

    if (ioctl(p2p_fd, GPU_P2P_MAP, &req) == 0 && req.num_segs > 0) {
      // Successfully mapped GPU memory
      b->iova = seg.dma_iova;
      fprintf(stderr, "INFO: GPU P2P mapped via kernel module: ptr=%p, iova=0x%llx\n",
              (void*)dptr, (unsigned long long)b->iova);
      close(p2p_fd);
      return b;
    }

    fprintf(stderr, "WARNING: GPU_P2P_MAP ioctl failed, falling back to pinned host\n");
    close(p2p_fd);
  } else {
    fprintf(stderr, "WARNING: /dev/gpu_p2p_nvme not available, falling back to pinned host\n");
  }

  // Fallback to pinned host memory
  cuMemFree(dptr);
  delete b;

  void* host_ptr = nullptr;
  cudaError_t cuda_err = cudaHostAlloc(&host_ptr, buffer_size, cudaHostAllocPortable);
  if (cuda_err != cudaSuccess) {
    fprintf(stderr, "ERROR: cudaHostAlloc fallback failed: %s\n", cudaGetErrorString(cuda_err));
    return nullptr;
  }

  // Map to IOVA for NVMe DMA
  uint64_t iova = 0;
  if (host_map_iova(host_ptr, buffer_size, &iova) != 0) {
    fprintf(stderr, "ERROR: Failed to map pinned host memory to IOVA\n");
    cudaFreeHost(host_ptr);
    return nullptr;
  }

  fprintf(stderr, "INFO: Using pinned host memory fallback: ptr=%p, iova=0x%llx\n",
          host_ptr, (unsigned long long)iova);

  b = new Buffer();
  b->addr = host_ptr;
  b->bytes = buffer_size;
  b->iova = iova;
  b->mem_type = MemoryType::PINNED_HOST;
  b->consecutive = Consecutive::CONSECUTIVE;
  return b;
}

extern "C" void nvme_cuda_device_buffer_destroy(Buffer* b){
  if (!b) return;

  if (b->addr) {
    if (b->mem_type == MemoryType::PINNED_HOST) {
      // Unmap from IOVA first
      if (b->iova != 0) {
        host_unmap_iova(b->addr, b->bytes, b->iova);
      }
      // Free pinned host memory
      cudaError_t cuda_err = cudaFreeHost(b->addr);
      if (cuda_err != cudaSuccess) {
        fprintf(stderr, "ERROR: cudaFreeHost failed: %s\n", cudaGetErrorString(cuda_err));
      }
    } else if (b->mem_type == MemoryType::PINNED_DEVICE) {
      // Use CUDA Driver API for GPU memory cleanup
      CUresult res = cuMemFree((CUdeviceptr)b->addr);
      if (res != CUDA_SUCCESS) {
        const char* err_str = nullptr;
        cuGetErrorString(res, &err_str);
        fprintf(stderr, "ERROR: cuMemFree failed: %d (%s)\n", res, err_str ? err_str : "unknown");
      }
    }
  }
  delete b;
}

// ============================================================================
// CUDA P2P Token Queries
// ============================================================================

extern "C" int nvme_cuda_query_p2p_tokens(const void* device_ptr,
                                           CudaP2PTokens* out_tokens) {
  if (!device_ptr || !out_tokens) return -1;

  CUresult res = cuInit(0);
  // cuInit returns CUDA_SUCCESS even if already initialized
  if (res != CUDA_SUCCESS) {
    fprintf(stderr, "ERROR: cuInit failed: %d\n", res);
    return -static_cast<int>(res);
  }

  CUDA_POINTER_ATTRIBUTE_P2P_TOKENS tokens{};
  res = cuPointerGetAttribute(&tokens, CU_POINTER_ATTRIBUTE_P2P_TOKENS,
                              reinterpret_cast<CUdeviceptr>(device_ptr));
  if (res != CUDA_SUCCESS) {
    const char* err_str = nullptr;
    cuGetErrorString(res, &err_str);
    fprintf(stderr, "ERROR: cuPointerGetAttribute(P2P_TOKENS) failed: %d (%s)\n",
            res, err_str ? err_str : "unknown");
    fprintf(stderr, "       device_ptr=%p\n", device_ptr);
    return -static_cast<int>(res);
  }

  out_tokens->p2p_token = tokens.p2pToken;
  out_tokens->va_space = tokens.vaSpaceToken;

  // Debug output
  DEBUG_LOG("P2P tokens retrieved: p2p_token=0x%llx, va_space=0x%x",
            (unsigned long long)tokens.p2pToken, tokens.vaSpaceToken);

  return 0;
}

// ============================================================================
// GPU Queue Setup (merged from nvme_gpu_submit_setup.cpp)
// ============================================================================

namespace {

constexpr const char* kP2PDevicePath = "/dev/gpu_p2p_nvme";

uint64_t parse_bdf(const char* bdf_str)
{
	if (!bdf_str)
		return 0;

	unsigned int domain = 0, bus = 0, device = 0, function = 0;
	if (std::sscanf(bdf_str, "%x:%x:%x.%x", &domain, &bus, &device, &function) != 4)
		return 0;

	return (static_cast<uint64_t>(domain) << 32) |
	       (static_cast<uint64_t>(bus) << 16) |
	       (static_cast<uint64_t>((device << 3) | function));
}

struct WrapperApi {
	using MapFn = int (*)(int, struct gpu_p2p_req*);
	using UnmapFn = int (*)(int, uint64_t);
	void* handle{nullptr};
	MapFn map_fn{nullptr};
	UnmapFn unmap_fn{nullptr};
	bool initialized{false};
};

WrapperApi& get_wrapper_api() {
	static WrapperApi api;
	return api;
}

bool ensure_wrapper_loaded() {
	auto& api = get_wrapper_api();
	if (api.initialized) {
		return api.map_fn != nullptr;
	}
	api.initialized = true;

	const char* candidates[] = {
		"libgpu_p2p_wrapper.so",
		"/usr/local/lib/libgpu_p2p_wrapper.so",
		nullptr};

	for (const char** path = candidates; *path; ++path) {
		api.handle = dlopen(*path, RTLD_LAZY | RTLD_LOCAL);
		if (api.handle) {
			break;
		}
	}

	if (!api.handle) {
		std::fprintf(stderr,
		             "gpu_p2p_wrapper: Not found (dlopen failed). "
		             "Install via Makefile.dual install in driver/.\n");
		return false;
	}

	api.map_fn = reinterpret_cast<WrapperApi::MapFn>(
		dlsym(api.handle, "gpu_p2p_map_buffer"));
	api.unmap_fn = reinterpret_cast<WrapperApi::UnmapFn>(
		dlsym(api.handle, "gpu_p2p_unmap_buffer"));

	if (!api.map_fn) {
		std::fprintf(stderr,
		             "gpu_p2p_wrapper: gpu_p2p_map_buffer symbol missing in loaded library\n");
		return false;
	}

	return true;
}

int map_buffer_with_wrapper(struct gpu_p2p_req* req) {
	if (!ensure_wrapper_loaded()) {
		return -1;
	}

	auto& api = get_wrapper_api();
	int rc = api.map_fn(-1, req);
	if (rc != 0) {
		std::fprintf(stderr,
		             "gpu_p2p_wrapper: gpu_p2p_map_buffer failed with rc=%d (p2p_token=0x%llx, va_space=0x%x)\n",
		             rc,
		             static_cast<unsigned long long>(req->p2p_token),
		             req->va_space);
	}
	return rc;
}

} // namespace

// One-time initialization for CUDA device flags (enables host pointer mapping)
static bool cuda_device_flags_initialized = false;
static void ensure_cuda_device_flags() {
	if (cuda_device_flags_initialized) return;

	// Enable mapping of pinned host memory to device address space
	// This must be done before any CUDA runtime API calls
	cudaError_t err = cudaSetDeviceFlags(cudaDeviceMapHost);
	if (err != cudaSuccess && err != cudaErrorSetOnActiveProcess) {
		std::fprintf(stderr, "WARNING: cudaSetDeviceFlags(cudaDeviceMapHost) failed: %s\n",
		             cudaGetErrorString(err));
		// Continue anyway - it may already be enabled
	}
	cuda_device_flags_initialized = true;
}

extern "C" int nvme_setup_gpu_queue(
	NvmeDevice* nvme_dev,
	const char* nvme_bdf,
	NvmeQueueStruct* out_gpu_queue
)
{
	if (!nvme_dev || !nvme_bdf || !out_gpu_queue) {
		std::fprintf(stderr, "nvme_setup_gpu_queue: Invalid arguments\n");
		return -1;
	}

	// Ensure CUDA device flags are set for host mapping
	ensure_cuda_device_flags();

	// Get IO queue from NVMe device
	Queue* iosq = nvme_get_iosq(nvme_dev);
	Queue* iocq = nvme_get_iocq(nvme_dev);

	if (!iosq || !iocq || !iosq->vaddr || !iocq->vaddr) {
		std::fprintf(stderr, "nvme_setup_gpu_queue: Invalid IO queues\n");
		return -1;
	}

	// Query CUDA P2P tokens
	CudaP2PTokens tokens{};
	// Use a dummy GPU pointer to get tokens (we need the GPU context tokens)
	void* dummy_gpu_ptr = nullptr;
	cudaMalloc(&dummy_gpu_ptr, 4096);
	int rc = nvme_cuda_query_p2p_tokens(dummy_gpu_ptr, &tokens);
	cudaFree(dummy_gpu_ptr);

	if (rc != 0) {
		std::fprintf(stderr, "nvme_setup_gpu_queue: Failed to query P2P tokens\n");
		return -1;
	}

	// Open GPU P2P device
	int fd = ::open(kP2PDevicePath, O_RDWR | O_CLOEXEC);
	if (fd < 0) {
		std::perror("open(/dev/gpu_p2p_nvme)");
		return -1;
	}

	uint64_t nvme_pci_bdf = parse_bdf(nvme_bdf);
	if (!nvme_pci_bdf) {
		std::fprintf(stderr, "nvme_setup_gpu_queue: Invalid NVMe BDF: %s\n", nvme_bdf);
		::close(fd);
		return -1;
	}

	// Map NVMe queues to GPU
	struct gpu_p2p_nvme_queue_req queue_req{};
	queue_req.nvme_pci_bdf = nvme_pci_bdf;
	queue_req.sq_host_va = reinterpret_cast<uint64_t>(iosq->vaddr);
	queue_req.cq_host_va = reinterpret_cast<uint64_t>(iocq->vaddr);
	queue_req.p2p_token = tokens.p2p_token;
	queue_req.va_space = tokens.va_space;
	queue_req.qid = iosq->qid;
	queue_req.sq_depth = iosq->entries;
	queue_req.cq_depth = iocq->entries;
	queue_req.flags = 0;

	if (::ioctl(fd, GPU_P2P_MAP_NVME_QUEUES, &queue_req) < 0) {
		std::perror("ioctl(GPU_P2P_MAP_NVME_QUEUES)");
		::close(fd);
		return -1;
	}

	std::printf("Mapped NVMe queues: SQ VA=0x%lx CQ VA=0x%lx\n",
	            (unsigned long)queue_req.out.sq_gpu_va, (unsigned long)queue_req.out.cq_gpu_va);

	// Try to register VFIO queues directly with CUDA for GPU access
	// This eliminates the need for shadow queues and command copying!
	// cudaHostRegister CAN work on mmap'd memory if page-aligned

	size_t sq_size = queue_req.out.sq_depth * 64;  // NVMe command is 64 bytes
	size_t cq_size = queue_req.out.cq_depth * 16;  // NVMe completion is 16 bytes

	void* sq_host_ptr = reinterpret_cast<void*>(queue_req.out.sq_gpu_va);
	void* cq_host_ptr = reinterpret_cast<void*>(queue_req.out.cq_gpu_va);

	void* sq_dev_ptr = nullptr;
	void* cq_dev_ptr = nullptr;
	bool direct_vfio_access = false;

	// Try to register VFIO SQ with CUDA
	cudaError_t cuda_err = cudaHostRegister(sq_host_ptr, sq_size, cudaHostRegisterDefault);
	if (cuda_err == cudaSuccess) {
		cuda_err = cudaHostRegister(cq_host_ptr, cq_size, cudaHostRegisterDefault);
		if (cuda_err == cudaSuccess) {
			// Get device pointers for GPU access
			cuda_err = cudaHostGetDevicePointer(&sq_dev_ptr, sq_host_ptr, 0);
			if (cuda_err == cudaSuccess) {
				cuda_err = cudaHostGetDevicePointer(&cq_dev_ptr, cq_host_ptr, 0);
				if (cuda_err == cudaSuccess) {
					direct_vfio_access = true;
					std::printf("SUCCESS: VFIO queues registered with CUDA - NO shadow queues needed!\n");
					std::printf("  GPU can write directly to VFIO SQ, daemon only rings doorbell\n");
				}
			}
			if (!direct_vfio_access) {
				cudaHostUnregister(cq_host_ptr);
				cudaHostUnregister(sq_host_ptr);
			}
		} else {
			cudaHostUnregister(sq_host_ptr);
		}
	}

	if (!direct_vfio_access) {
		std::printf("cudaHostRegister on VFIO queues failed: %s\n", cudaGetErrorString(cuda_err));
		std::printf("Falling back to shadow queue approach (slower due to command copying)\n");
	}

	// Fallback: Allocate shadow queues if direct VFIO access failed
	void* sq_shadow_ptr = nullptr;
	void* cq_shadow_ptr = nullptr;

	if (!direct_vfio_access) {
		cuda_err = cudaHostAlloc(&sq_shadow_ptr, sq_size,
		                          cudaHostAllocMapped | cudaHostAllocPortable);
		if (cuda_err != cudaSuccess) {
			std::fprintf(stderr, "nvme_setup_gpu_queue: Failed to allocate shadow SQ: %s\n",
			             cudaGetErrorString(cuda_err));
			::close(fd);
			return -1;
		}

		cuda_err = cudaHostAlloc(&cq_shadow_ptr, cq_size,
		                         cudaHostAllocMapped | cudaHostAllocPortable);
		if (cuda_err != cudaSuccess) {
			std::fprintf(stderr, "nvme_setup_gpu_queue: Failed to allocate shadow CQ: %s\n",
			             cudaGetErrorString(cuda_err));
			cudaFreeHost(sq_shadow_ptr);
			::close(fd);
			return -1;
		}

		// Initialize shadow queues
		std::memset(sq_shadow_ptr, 0, sq_size);
		std::memset(cq_shadow_ptr, 0, cq_size);

		// Get device pointers for GPU access
		cuda_err = cudaHostGetDevicePointer(&sq_dev_ptr, sq_shadow_ptr, 0);
		if (cuda_err != cudaSuccess) {
			std::fprintf(stderr, "nvme_setup_gpu_queue: Failed to get SQ device pointer: %s\n",
			             cudaGetErrorString(cuda_err));
			cudaFreeHost(sq_shadow_ptr);
			cudaFreeHost(cq_shadow_ptr);
			::close(fd);
			return -1;
		}

		cuda_err = cudaHostGetDevicePointer(&cq_dev_ptr, cq_shadow_ptr, 0);
		if (cuda_err != cudaSuccess) {
			std::fprintf(stderr, "nvme_setup_gpu_queue: Failed to get CQ device pointer: %s\n",
			             cudaGetErrorString(cuda_err));
			cudaFreeHost(sq_shadow_ptr);
			cudaFreeHost(cq_shadow_ptr);
			::close(fd);
			return -1;
		}
	}

	// Check pointer attributes to understand memory type
	cudaPointerAttributes sq_attr, cq_attr;
	cudaPointerGetAttributes(&sq_attr, sq_dev_ptr);
	cudaPointerGetAttributes(&cq_attr, cq_dev_ptr);
	std::printf("SQ host ptr: %p, dev ptr: %p, type=%d, device=%d\n",
	            direct_vfio_access ? sq_host_ptr : sq_shadow_ptr, sq_dev_ptr, sq_attr.type, sq_attr.device);
	std::printf("CQ host ptr: %p, dev ptr: %p, type=%d, device=%d\n",
	            direct_vfio_access ? cq_host_ptr : cq_shadow_ptr, cq_dev_ptr, cq_attr.type, cq_attr.device);

	// Update queue_req with device pointers
	queue_req.out.sq_gpu_va = reinterpret_cast<uint64_t>(sq_dev_ptr);
	queue_req.out.cq_gpu_va = reinterpret_cast<uint64_t>(cq_dev_ptr);

	if (direct_vfio_access) {
		std::printf("DIRECT VFIO ACCESS: GPU writes directly to VFIO SQ @ %p (dev=%p)\n",
		            sq_host_ptr, sq_dev_ptr);
		std::printf("  Daemon only needs to ring doorbell - NO command copying!\n");
	} else {
		std::printf("Allocated shadow queue memory: SQ=%zu bytes @ %p (dev=%p), CQ=%zu bytes @ %p (dev=%p)\n",
		            sq_size, sq_shadow_ptr, sq_dev_ptr, cq_size, cq_shadow_ptr, cq_dev_ptr);
		std::printf("Original VFIO queues: SQ=%p, CQ=%p\n", sq_host_ptr, cq_host_ptr);
		std::printf("NOTE: Host daemon must copy GPU shadow SQ -> VFIO SQ and VFIO CQ -> GPU shadow CQ\n");
	}

	// Fill GPU queue descriptor
	std::memset(out_gpu_queue, 0, sizeof(NvmeQueueStruct));

	// Shadow queues (GPU-accessible, managed memory)
	out_gpu_queue->sq_base = reinterpret_cast<NvmeCmd*>(queue_req.out.sq_gpu_va);
	out_gpu_queue->cq_base = reinterpret_cast<NvmeCqe*>(queue_req.out.cq_gpu_va);
	out_gpu_queue->item_size = nvme_get_item_size(nvme_dev);
	out_gpu_queue->page_size = static_cast<uint32_t>(nvme_get_page_size(nvme_dev));
	out_gpu_queue->nsid = queue_req.out.qid == 0 ? 0 : 1;  // IO queue usually namespace 1
	out_gpu_queue->doorbell_mode = DOORBELL_MODE_GPU_DBC_DAEMON;  // GPU writes shadow DB, daemon rings MMIO

	out_gpu_queue->sq_depth = queue_req.out.sq_depth;
	out_gpu_queue->cq_depth = queue_req.out.cq_depth;
	out_gpu_queue->qid = queue_req.out.qid;
	out_gpu_queue->sq_phase = queue_req.out.sq_phase;
	out_gpu_queue->cq_phase = queue_req.out.cq_phase;
	out_gpu_queue->sq_tail = queue_req.out.sq_tail;
	out_gpu_queue->sq_internal_tail = queue_req.out.sq_tail;  // Initialize internal tail same as external
	out_gpu_queue->cq_head = queue_req.out.cq_head;

	// Store original VFIO queue pointers for daemon (Mode 5)
	// If direct_vfio_access, sq_base == vfio_sq_base (same memory), daemon skips copy
	// If shadow queues, vfio_sq_base points to original VFIO memory for daemon to copy to
	if (direct_vfio_access) {
		// GPU writes directly to VFIO queues - no copy needed
		out_gpu_queue->vfio_sq_base = nullptr;  // Signal daemon: no copy needed
		out_gpu_queue->vfio_cq_base = nullptr;
	} else {
		// Shadow queue mode - daemon must copy shadow -> VFIO
		out_gpu_queue->vfio_sq_base = reinterpret_cast<NvmeCmd*>(sq_host_ptr);
		out_gpu_queue->vfio_cq_base = reinterpret_cast<NvmeCqe*>(cq_host_ptr);
	}

	// Get MMIO doorbell pointers from NVMe device
	out_gpu_queue->mmio_sq_doorbell = reinterpret_cast<volatile uint32_t*>(iosq->db);
	out_gpu_queue->mmio_cq_doorbell = reinterpret_cast<volatile uint32_t*>(iocq->db);

	::close(fd);

	std::printf("GPU queue setup complete: qid=%u sq_depth=%u cq_depth=%u\n",
	            out_gpu_queue->qid, out_gpu_queue->sq_depth, out_gpu_queue->cq_depth);
	if (direct_vfio_access) {
		std::printf("  DIRECT VFIO ACCESS MODE: GPU writes directly to VFIO SQ=%p\n",
		            out_gpu_queue->sq_base);
		std::printf("  Daemon only rings doorbell, NO command copying!\n");
	} else {
		std::printf("  Shadow SQ=%p, Shadow CQ=%p\n",
		            out_gpu_queue->sq_base, out_gpu_queue->cq_base);
		std::printf("  VFIO SQ=%p, VFIO CQ=%p\n",
		            out_gpu_queue->vfio_sq_base, out_gpu_queue->vfio_cq_base);
	}
	std::printf("  MMIO doorbells: SQ=%p, CQ=%p\n",
	            out_gpu_queue->mmio_sq_doorbell, out_gpu_queue->mmio_cq_doorbell);

	return 0;
}

// ============================================================================
// GPU Completion Queue Creation (Mode 5/6)
// ============================================================================

extern "C" int nvme_create_gpu_completion_queue(
	NvmeDevice* nvme_dev,
	uint16_t cqid,
	uint16_t cq_depth,
	void** gpu_cq_dev_ptr,
	uint64_t* gpu_cq_iova
)
{
	if (!nvme_dev || !gpu_cq_dev_ptr || !gpu_cq_iova) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: Invalid arguments\n");
		return -1;
	}

	if ((cq_depth & (cq_depth - 1)) != 0 || cq_depth < 2 || cq_depth > 65536) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: Invalid cq_depth %u (must be power of 2, 2-65536)\n", cq_depth);
		return -2;
	}

	// Calculate CQ size (16 bytes per completion entry)
	const size_t cq_size = cq_depth * sizeof(NvmeCqe);  // 16 bytes per CQE

	// Allocate GPU memory for completion queue
	void* cq_gpu_ptr = nullptr;
	cudaError_t cuda_err = cudaMalloc(&cq_gpu_ptr, cq_size);
	if (cuda_err != cudaSuccess) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: cudaMalloc failed: %s\n",
		            cudaGetErrorString(cuda_err));
		return -3;
	}

	// Zero initialize the CQ
	cuda_err = cudaMemset(cq_gpu_ptr, 0, cq_size);
	if (cuda_err != cudaSuccess) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: cudaMemset failed: %s\n",
		            cudaGetErrorString(cuda_err));
		cudaFree(cq_gpu_ptr);
		return -4;
	}

	std::fprintf(stderr, "INFO: Allocated GPU CQ: ptr=%p, size=%zu bytes (%u entries)\n",
	            cq_gpu_ptr, cq_size, cq_depth);

	// Get P2P tokens for GPU memory
	CudaP2PTokens tokens{};
	if (nvme_cuda_query_p2p_tokens(cq_gpu_ptr, &tokens) != 0) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: Failed to query P2P tokens\n");
		cudaFree(cq_gpu_ptr);
		return -5;
	}

	// Request P2P mapping to get IOVA
	struct gpu_p2p_req req{};
	req.gpu_va = reinterpret_cast<uint64_t>(cq_gpu_ptr);
	req.bytes = cq_size;
	// Use NVME_BDF if available so the core driver can build the correct IOVA mapping
	const char* nvme_bdf_env = std::getenv("NVME_BDF");
	req.nvme_pci_bdf = nvme_bdf_env ? parse_bdf(nvme_bdf_env) : 0;
	req.p2p_token = tokens.p2p_token;
	req.va_space = tokens.va_space;
	req.max_segs = 1;
	req.out_user_ptr = 0;

	// Single segment output buffer for the CQ
	struct gpu_p2p_seg cq_seg{};
	req.out_user_ptr = reinterpret_cast<uint64_t>(&cq_seg);
	int map_rc = map_buffer_with_wrapper(&req);
	if (map_rc != 0) {
		std::fprintf(stderr,
		             "nvme_create_gpu_completion_queue: P2P mapping failed (rc=%d). "
		             "Ensure libgpu_p2p_wrapper is installed and modules are loaded.\n",
		             map_rc);
		cudaFree(cq_gpu_ptr);
		return -7;
	}

	if (req.num_segs == 0) {
		std::fprintf(stderr, "ERROR: GPU_P2P_MAP returned zero segments for CQ\n");
		cudaFree(cq_gpu_ptr);
		return -7;
	}

	uint64_t cq_iova = cq_seg.dma_iova;
	std::fprintf(stderr, "INFO: Mapped GPU CQ to IOVA: 0x%llx\n", (unsigned long long)cq_iova);

	// Use existing nvme_create_gpu_cq() from mapper_host to send admin command
	int rc = nvme_create_gpu_cq(nvme_dev, cqid, cq_gpu_ptr, cq_iova, cq_depth);
	if (rc != 0) {
		std::fprintf(stderr, "nvme_create_gpu_completion_queue: nvme_create_gpu_cq failed: %d\n", rc);
		// TODO: Unmap P2P and free GPU memory
		cudaFree(cq_gpu_ptr);
		return -8;
	}

	// Success - return GPU pointer and IOVA
	*gpu_cq_dev_ptr = cq_gpu_ptr;
	*gpu_cq_iova = cq_iova;

	std::fprintf(stderr, "INFO: GPU CQ created successfully: cqid=%u, depth=%u, GPU ptr=%p, IOVA=0x%llx\n",
	            cqid, cq_depth, cq_gpu_ptr, (unsigned long long)cq_iova);

	return 0;
}
