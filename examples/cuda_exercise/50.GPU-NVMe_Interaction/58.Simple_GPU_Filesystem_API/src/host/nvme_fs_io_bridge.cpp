/**
 * @file nvme_fs_io_bridge.cpp
 * @brief Bridge implementation connecting Module 58 filesystem to Module 53-57 NVMe I/O
 *
 * This file provides the actual implementation of read_blocks/write_blocks
 * using Module 53's host I/O capabilities. It overrides the weak symbols
 * from nvme_fs_io_stubs.cpp with real NVMe operations.
 *
 * @author Integration Implementation
 * @date 2025-11-20
 */

#include "mapper/mapper_host.h"     // Module 53: NvmeDevice
#include "io/host_io_host_mem.h"      // Module 53: host_io_read/write
#include <cstring>
#include <stdexcept>

namespace nvme_fs {

/**
 * @brief Read blocks from NVMe device using Module 53 API
 *
 * This implementation uses Module 53's host I/O functions to perform
 * actual NVMe read operations. It bridges the filesystem layer with
 * the low-level NVMe driver.
 *
 * @param nvme_device Pointer to NvmeDevice from Module 53
 * @param lba Starting logical block address
 * @param count Number of blocks to read
 * @param buffer Output buffer (must be at least count * block_size bytes)
 */
void read_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, void* buffer) {
    if (!nvme_device || !buffer) {
        throw std::invalid_argument("Invalid device or buffer pointer");
    }

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device);

    // Get device parameters
    std::uint32_t lba_size = nvme_get_lba_size(dev);
    std::uint64_t num_lbas = nvme_get_num_lbas(dev);

    // Validate request
    if (lba + count > num_lbas) {
        throw std::out_of_range("Read request exceeds device capacity");
    }

    std::size_t bytes_to_read = count * lba_size;

    // Use Module 53's host I/O function
    int result = host_io_read(dev, lba, buffer, bytes_to_read);

    if (result != 0) {
        throw std::runtime_error("NVMe read operation failed");
    }
}

/**
 * @brief Write blocks to NVMe device using Module 53 API
 *
 * This implementation uses Module 53's host I/O functions to perform
 * actual NVMe write operations. It bridges the filesystem layer with
 * the low-level NVMe driver.
 *
 * @param nvme_device Pointer to NvmeDevice from Module 53
 * @param lba Starting logical block address
 * @param count Number of blocks to write
 * @param buffer Input buffer (must contain at least count * block_size bytes)
 */
void write_blocks(void* nvme_device, std::uint64_t lba, std::uint64_t count, const void* buffer) {
    if (!nvme_device || !buffer) {
        throw std::invalid_argument("Invalid device or buffer pointer");
    }

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device);

    // Get device parameters
    std::uint32_t lba_size = nvme_get_lba_size(dev);
    std::uint64_t num_lbas = nvme_get_num_lbas(dev);

    // Validate request
    if (lba + count > num_lbas) {
        throw std::out_of_range("Write request exceeds device capacity");
    }

    std::size_t bytes_to_write = count * lba_size;

    // Use Module 53's host I/O function
    int result = host_io_write(dev, lba, buffer, bytes_to_write);

    if (result != 0) {
        throw std::runtime_error("NVMe write operation failed");
    }
}

}  // namespace nvme_fs

// ============================================================================
// GPU-Accelerated Variants (Future Integration with Modules 55-57)
// ============================================================================

#ifdef ENABLE_GPU_IO

#include "io/cuda_io_gpu_mem.h"       // Module 55: GPU memory I/O
#include "doorbell/nvme_doorbell.h"   // Module 56: GPU doorbell modes

namespace nvme_fs {

/**
 * @brief Read blocks directly to GPU memory using Module 55
 *
 * This function enables GPUDirect Storage-like functionality by reading
 * NVMe data directly into GPU memory without CPU staging.
 *
 * @param nvme_device Pointer to NvmeDevice from Module 53
 * @param lba Starting logical block address
 * @param count Number of blocks to read
 * @param gpu_buffer GPU memory buffer (allocated with cudaMalloc)
 */
void read_blocks_gpu(void* nvme_device, std::uint64_t lba, std::uint64_t count, void* gpu_buffer) {
    if (!nvme_device || !gpu_buffer) {
        throw std::invalid_argument("Invalid device or GPU buffer pointer");
    }

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device);
    std::uint32_t lba_size = nvme_get_lba_size(dev);
    std::size_t bytes_to_read = count * lba_size;

    // Use Module 55's GPU memory I/O function
    int result = cuda_io_read_gpu_mem(dev, lba, gpu_buffer, bytes_to_read);

    if (result != 0) {
        throw std::runtime_error("GPU NVMe read operation failed");
    }
}

/**
 * @brief Write blocks from GPU memory using Module 55
 *
 * @param nvme_device Pointer to NvmeDevice from Module 53
 * @param lba Starting logical block address
 * @param count Number of blocks to write
 * @param gpu_buffer GPU memory buffer (allocated with cudaMalloc)
 */
void write_blocks_gpu(void* nvme_device, std::uint64_t lba, std::uint64_t count, const void* gpu_buffer) {
    if (!nvme_device || !gpu_buffer) {
        throw std::invalid_argument("Invalid device or GPU buffer pointer");
    }

    NvmeDevice* dev = static_cast<NvmeDevice*>(nvme_device);
    std::uint32_t lba_size = nvme_get_lba_size(dev);
    std::size_t bytes_to_write = count * lba_size;

    // Use Module 55's GPU memory I/O function
    int result = cuda_io_write_gpu_mem(dev, lba, gpu_buffer, bytes_to_write);

    if (result != 0) {
        throw std::runtime_error("GPU NVMe write operation failed");
    }
}

}  // namespace nvme_fs

#endif  // ENABLE_GPU_IO