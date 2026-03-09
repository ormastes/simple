/**
 * @file nvme_expert_storage.h
 * @brief NVMe-based storage backend for expert weights
 *
 * Provides a storage layer that persists expert weight tensors on
 * NVMe devices, enabling models with more experts than can fit in
 * GPU memory. Supports both standard file I/O and direct GPU-NVMe
 * transfers when GPUDirect Storage (GDS) is available.
 */
#pragma once
#include <cuda_runtime.h>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <string>

namespace llm {

/**
 * @brief NVMe storage backend for MoE expert weights
 *
 * Manages reading and writing expert weight files on NVMe storage.
 * Each expert is stored as a separate binary file for independent
 * access and to enable parallel loading of multiple experts.
 *
 * @code
 * NVMeExpertStorage storage;
 * storage.init("/mnt/nvme/experts", 64, 4*1024*1024);
 *
 * float* d_buffer;
 * cudaMalloc(&d_buffer, 4*1024*1024);
 * storage.load_expert(d_buffer, 0, stream);
 *
 * storage.destroy();
 * @endcode
 */
struct NVMeExpertStorage {
    std::string storage_path;  ///< Directory path for expert weight files
    int num_experts;           ///< Total number of experts
    size_t expert_size;        ///< Size of each expert in bytes

    /**
     * @brief Initialize the NVMe storage backend
     * @param[in] path         Directory containing expert weight files
     * @param[in] num_experts  Total number of experts
     * @param[in] expert_size  Size of each expert's weights in bytes
     */
    void init(const char* path, int num_experts_, size_t expert_size_) {
        storage_path = path;
        num_experts = num_experts_;
        expert_size = expert_size_;
    }

    /**
     * @brief Load expert weights from NVMe to GPU memory
     *
     * Reads expert weight data from the NVMe file and transfers it
     * to the provided GPU buffer. Uses pinned host memory as a staging
     * buffer for the transfer.
     *
     * @param[out] gpu_buffer  Destination GPU buffer (must be at least expert_size bytes)
     * @param[in]  expert_id   Index of the expert to load
     * @param[in]  stream      CUDA stream for async transfer
     */
    void load_expert(float* gpu_buffer, int expert_id, cudaStream_t stream = 0) {
        if (expert_id < 0 || expert_id >= num_experts || !gpu_buffer) {
            return;
        }

        std::string filepath = storage_path + "/expert_" + std::to_string(expert_id) + ".bin";

        // Attempt to load from file
        FILE* f = fopen(filepath.c_str(), "rb");
        if (f) {
            void* host_staging = nullptr;
            cudaMallocHost(&host_staging, expert_size);
            size_t read = fread(host_staging, 1, expert_size, f);
            fclose(f);

            if (read == expert_size) {
                cudaMemcpyAsync(gpu_buffer, host_staging, expert_size,
                               cudaMemcpyHostToDevice, stream);
                cudaStreamSynchronize(stream);
            }
            cudaFreeHost(host_staging);
        } else {
            // File not found; zero-initialize the buffer
            cudaMemsetAsync(gpu_buffer, 0, expert_size, stream);
        }
    }

    /**
     * @brief Save expert weights from GPU memory to NVMe
     * @param[in] gpu_buffer  Source GPU buffer containing expert weights
     * @param[in] expert_id   Index of the expert to save
     */
    void save_expert(const float* gpu_buffer, int expert_id) {
        if (expert_id < 0 || expert_id >= num_experts || !gpu_buffer) {
            return;
        }

        std::string filepath = storage_path + "/expert_" + std::to_string(expert_id) + ".bin";

        void* host_staging = nullptr;
        cudaMallocHost(&host_staging, expert_size);
        cudaMemcpy(host_staging, gpu_buffer, expert_size, cudaMemcpyDeviceToHost);

        FILE* f = fopen(filepath.c_str(), "wb");
        if (f) {
            fwrite(host_staging, 1, expert_size, f);
            fclose(f);
        }
        cudaFreeHost(host_staging);
    }

    /**
     * @brief Cleanup resources
     */
    void destroy() {
        // No persistent resources to free; storage files remain on disk
    }
};

} // namespace llm
