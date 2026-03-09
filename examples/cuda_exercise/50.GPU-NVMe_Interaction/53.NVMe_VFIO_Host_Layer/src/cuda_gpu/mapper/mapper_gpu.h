/**
 * @file mapper_gpu.h
 * @brief GPU-side NVMe memory mapper interface
 *
 * Provides CUDA-based operations for:
 * - GPU device buffer allocation for NVMe DMA
 * - CUDA P2P token queries for GPU-NVMe mapping
 * - GPU queue setup for NVMe submission
 */

#pragma once
#include <cstddef>
#include <cstdint>

#include "mapper/mapper_host.h"  // For NvmeDevice, NvmeQueueStruct
#include "memory/memory_types.h"   // For Buffer, DmaBuf definitions

/**
 * @brief CUDA P2P tokens for GPUDirect RDMA
 *
 * These tokens are obtained from CUDA driver and passed to kernel module
 * for P2P mapping setup.
 */
struct CudaP2PTokens {
    std::uint64_t p2p_token;  ///< P2P token from nvidia_p2p API
    std::uint32_t va_space;   ///< Virtual address space token
};

extern "C" {

/**
 * @brief Allocates CUDA device memory for NVMe DMA operations
 *
 * Creates a consecutive GPU device buffer using CUDA Driver API (cuMemAlloc).
 * The buffer is suitable for P2P DMA with NVMe devices when mapped via kernel
 * module. Returns a Buffer structure with MemoryType::PINNED_DEVICE.
 *
 * @param[in] buffer_size Size of buffer to allocate in bytes
 * @return Pointer to Buffer structure on success, nullptr on failure
 *
 * @note Requires CUDA context to be initialized
 * @note P2P tokens are queried but IOVA mapping requires separate kernel ioctl
 * @warning Buffer must be freed with nvme_cuda_device_buffer_destroy()
 */
Buffer* nvme_gpu_create_cuda_pinned_consecutive_buffer(std::size_t buffer_size);

/**
 * @brief Destroys CUDA device buffer allocated by nvme_gpu_create_cuda_pinned_consecutive_buffer
 *
 * Frees GPU device memory using CUDA Driver API (cuMemFree) and deletes
 * the Buffer structure.
 *
 * @param[in] buffer Pointer to Buffer structure to destroy (may be nullptr)
 *
 * @note Safe to call with nullptr
 */
void nvme_cuda_device_buffer_destroy(Buffer* buffer);

/**
 * @brief Queries CUDA P2P tokens for a GPU device pointer
 *
 * Retrieves P2P tokens (p2p_token and va_space) required for GPU-NVMe
 * P2P mapping via kernel module. These tokens are used by nvidia_p2p_get_pages()
 * to establish DMA mappings.
 *
 * @param[in]  device_ptr GPU device pointer to query
 * @param[out] out_tokens Structure to receive P2P tokens
 * @return 0 on success, negative error code on failure
 *
 * @note Requires CUDA context to be initialized
 * @warning device_ptr must be valid GPU memory allocated with cuMemAlloc or cudaMalloc
 */
int nvme_cuda_query_p2p_tokens(const void* device_ptr,
                               CudaP2PTokens* out_tokens);

/**
 * @brief Sets up GPU-accessible NVMe queue structures with P2P mapping
 *
 * Maps NVMe submission/completion queues and doorbells to GPU address space
 * using the gpu_p2p_nvme kernel module. Enables GPU kernels to directly
 * submit NVMe commands without CPU involvement.
 *
 * @param[in]  nvme_dev      NVMe device handle from nvme_open()
 * @param[in]  nvme_bdf      NVMe device PCI address (format: "domain:bus:dev.func")
 * @param[out] out_gpu_queue GPU queue descriptor with mapped queue addresses
 * @return 0 on success, -1 on failure
 *
 * @note Requires /dev/gpu_p2p_nvme kernel module to be loaded
 * @warning nvme_dev must have valid IO queues already created
 * @warning nvme_bdf must match the device used to open nvme_dev
 */
int nvme_setup_gpu_queue(NvmeDevice* nvme_dev,
                         const char* nvme_bdf,
                         NvmeQueueStruct* out_gpu_queue);

/**
 * @brief Creates a GPU-resident completion queue for Mode 5/6
 *
 * Allocates GPU VRAM for the completion queue and configures the NVMe controller
 * to DMA completion entries directly to GPU memory via P2P. This enables
 * GPU kernels to poll completions without CPU involvement.
 *
 * @param[in]  nvme_dev        NVMe device handle
 * @param[in]  cqid            Completion queue ID (1-65535)
 * @param[in]  cq_depth        Queue depth (power of 2, 2-65536)
 * @param[out] gpu_cq_dev_ptr  GPU device pointer for allocated CQ
 * @param[out] gpu_cq_iova     IOVA mapped for NVMe DMA access
 * @return 0 on success, negative error code on failure
 *
 * @note Requires P2P kernel module and IOMMU support
 * @note CQ must be paired with SQ via nvme_create_host_sq_for_cq()
 * @warning GPU memory must remain allocated for lifetime of queue
 *
 * **Usage Example:**
 * ```cpp
 * void* cq_gpu_ptr;
 * uint64_t cq_iova;
 * int rc = nvme_create_gpu_completion_queue(dev, 2, 64, &cq_gpu_ptr, &cq_iova);
 * if (rc == 0) {
 *     // CQ is now in GPU VRAM, create matching SQ
 *     nvme_create_host_sq_for_cq(dev, 64, 2);
 * }
 * ```
 */
int nvme_create_gpu_completion_queue(NvmeDevice* nvme_dev,
                                     uint16_t cqid,
                                     uint16_t cq_depth,
                                     void** gpu_cq_dev_ptr,
                                     uint64_t* gpu_cq_iova);

}
