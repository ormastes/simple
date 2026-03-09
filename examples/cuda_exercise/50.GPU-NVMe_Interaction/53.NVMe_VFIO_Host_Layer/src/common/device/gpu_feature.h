/**
 * @file gpu_feature.h
 * @brief GPU device feature detection and capabilities
 *
 * Detects CUDA GPUs and reports:
 * - CUDA availability and version
 * - Device compute capability
 * - P2P DMA support
 * - Memory information
 * - NVLink connectivity
 */

#pragma once
#include "feature.h"
#include "cuda_utils.h"
#include <cuda_runtime.h>
#include <vector>

/**
 * @brief GPU device features and capabilities
 *
 * Represents a single GPU device and its features.
 * Use get_all_gpus() to enumerate all available GPUs.
 */
class GpuFeature : public Feature {
public:
    /**
     * @brief Construct GPU feature detector for specific device
     * @param device_id CUDA device ID (0-based)
     */
    explicit GpuFeature(int device_id = 0);

    // Feature interface
    bool is_available() const override { return cuda_available_; }
    string get_name() const override;
    string get_description() const override;
    void print(bool verbose = false) const override;

    // GPU-specific queries
    int get_device_id() const { return device_id_; }
    int get_compute_major() const { return compute_major_; }
    int get_compute_minor() const { return compute_minor_; }

    /**
     * @brief Check if CUDA is available at all
     * @return true if CUDA runtime is functional
     */
    bool has_cuda() const { return cuda_available_; }

    /**
     * @brief Check if P2P DMA is supported to another GPU
     * @param peer_device_id Target GPU device ID
     * @return true if P2P is supported between this GPU and peer
     */
    bool has_p2p_to_gpu(int peer_device_id) const;

    /**
     * @brief Check if this GPU can access NVMe via P2P
     * @return Support level for GPU-NVMe P2P DMA
     *
     * @note FULL support requires:
     *   - BAR1 size >= 256MB (for large transfers)
     *   - GPU in IOMMU group (check host features)
     *   - gpu_p2p_nvme kernel module loaded
     */
    SupportLevel get_nvme_p2p_support() const { return nvme_p2p_support_; }

    /**
     * @brief Get total device memory in bytes
     */
    size_t get_total_memory() const { return total_memory_; }

    /**
     * @brief Get BAR1 size in bytes
     * @return BAR1 size (0 if unavailable)
     *
     * BAR1 is used for P2P transfers. Larger BAR1 = better P2P performance.
     */
    size_t get_bar1_size() const { return bar1_size_; }

    /**
     * @brief Check if Unified Memory (UVM) is supported
     */
    bool has_unified_memory() const { return unified_memory_; }

    /**
     * @brief Get PCI bus ID (e.g., "0000:01:00.0")
     */
    string get_pci_bus_id() const { return pci_bus_id_; }

private:
    void detect_features();
    void detect_p2p_support();

    int device_id_;
    bool cuda_available_{false};
    int compute_major_{0};
    int compute_minor_{0};
    string device_name_;
    string pci_bus_id_;
    size_t total_memory_{0};
    size_t bar1_size_{0};
    bool unified_memory_{false};
    SupportLevel nvme_p2p_support_{SupportLevel::NOT_SUPPORTED};
    cudaDeviceProp props_{};
};

/**
 * @brief Enumerate all available GPUs
 * @return Vector of GpuFeature objects for each detected GPU
 *
 * @code
 * auto gpus = get_all_gpus();
 * for (const auto& gpu : gpus) {
 *     gpu.print(true);  // Print detailed info
 * }
 * @endcode
 */
std::vector<GpuFeature> get_all_gpus();
