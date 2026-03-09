/**
 * @file device_detector.h
 * @brief Unified device detection interface
 */

#pragma once
#include "feature.h"
#include "gpu_feature.h"
#include "nvme_feature.h"
#include "host_feature.h"
#include <vector>

/**
 * @brief Device selection requirements
 *
 * Specifies which features are required for device selection.
 * Unmet requirements result in nullptr returns in SelectedDevices.
 */
struct DeviceRequirements {
    // GPU requirements
    bool require_cuda{false};                ///< CUDA must be available
    bool require_gpu_pinned_memory{false};   ///< Unified addressing (pinned memory support)
    bool require_gpu_p2p{false};             ///< GPU-NVMe P2P DMA (FULL support)
    size_t min_gpu_memory{0};                ///< Minimum GPU memory in bytes

    // NVMe requirements
    bool require_nvme{false};                ///< At least one NVMe device
    bool require_shadow_doorbell{false};     ///< Shadow doorbell support (PARTIAL or FULL)
    bool require_full_shadow_doorbell{false};///< Require FULL shadow doorbell/DBC support
    bool require_nvme_p2p{false};            ///< NVMe P2P DMA (FULL support)
    bool require_nvme_vfio{false};           ///< NVMe device bound to vfio-pci
    uint64_t min_nvme_capacity{0};           ///< Minimum NVMe capacity in bytes
    std::string specific_nvme_bdf;           ///< Specific NVMe PCI BDF (empty = auto-select)

    // GPU requirements (specific device)
    std::string specific_gpu_pci_id;         ///< Specific GPU PCI ID (empty = auto-select)

    // Host requirements
    bool require_vfio{false};                ///< VFIO support (FULL)
    bool require_host_p2p{false};            ///< Host P2P infrastructure (FULL)
    bool require_iommu{false};               ///< IOMMU enabled
    uint64_t min_host_memory{0};             ///< Minimum system RAM in bytes

    /**
     * @brief Preset: P2P DMA requirements
     * @return Requirements for GPU-NVMe P2P tests
     */
    static DeviceRequirements for_p2p() {
        DeviceRequirements req;
        req.require_cuda = true;
        req.require_gpu_pinned_memory = true;
        req.require_gpu_p2p = true;
        req.require_nvme = true;
        req.require_nvme_p2p = true;
        req.require_vfio = true;
        req.require_host_p2p = true;
        req.require_iommu = true;
        return req;
    }

    /**
     * @brief Preset: Host DMA (VFIO) requirements
     * @return Requirements for host-initiated NVMe I/O
     */
    static DeviceRequirements for_host_dma() {
        DeviceRequirements req;
        req.require_nvme = true;
        req.require_vfio = true;
        req.require_iommu = true;
        return req;
    }

    /**
     * @brief Preset: GPU compute only (no NVMe)
     * @return Requirements for GPU-only tests
     */
    static DeviceRequirements for_gpu_compute() {
        DeviceRequirements req;
        req.require_cuda = true;
        req.require_gpu_pinned_memory = true;
        return req;
    }

    /**
     * @brief Preset: Shadow doorbell testing
     * @return Requirements for shadow doorbell tests
     */
    static DeviceRequirements for_shadow_doorbell() {
        DeviceRequirements req;
        req.require_nvme = true;
        req.require_shadow_doorbell = true;
        req.require_full_shadow_doorbell = true;  // Prefer true DBC-capable devices
        req.require_vfio = true;
        req.require_iommu = true;
        return req;
    }
};

/**
 * @brief Selected devices result
 *
 * Contains pointers to selected devices from SystemFeatures.
 * Pointers are nullptr if requirements couldn't be met.
 */
struct SelectedDevices {
    const HostFeature* host{nullptr};   ///< Selected host (always same, system-wide)
    const GpuFeature* gpu{nullptr};     ///< Best GPU matching requirements
    const NvmeFeature* nvme{nullptr};   ///< Best NVMe matching requirements
    std::string host_log;               ///< Host selection log (failure reasons or empty string)
    std::string nvme_log;               ///< NVMe selection log (failure reasons or empty string)

    /**
     * @brief Check if all requirements were met
     * @return true if all requested devices were found
     */
    bool all_requirements_met() const {
        return host != nullptr;  // Host always present; gpu/nvme checked separately
    }

    /**
     * @brief Get description of selected devices
     * @return Multi-line string describing selection
     */
    string get_description() const;

    /**
     * @brief Print selected devices
     */
    void print() const;
};

/**
 * @brief Complete system device information
 *
 * Contains all detected devices and their features.
 */
struct SystemFeatures {
    HostFeature host;                    ///< Host system capabilities
    std::vector<GpuFeature> gpus;        ///< All detected GPUs
    std::vector<NvmeFeature> nvme_devs;  ///< All detected NVMe devices

    /**
     * @brief Check if system is ready for GPU-NVMe P2P
     * @return true if all requirements are met for P2P DMA
     *
     * Requirements:
     * - At least one GPU with FULL P2P support
     * - At least one NVMe device with FULL P2P support
     * - Host VFIO support is FULL
     * - Host P2P support is FULL
     */
    bool is_p2p_ready() const;

    /**
     * @brief Get summary of system capabilities
     * @return Multi-line string summarizing all features
     */
    string get_summary() const;

    /**
     * @brief Print all device information
     * @param verbose If true, print detailed information for each device
     */
    void print_all(bool verbose = false) const;

    /**
     * @brief Find GPU by device ID
     * @param device_id CUDA device ID
     * @return Pointer to GpuFeature or nullptr if not found
     */
    const GpuFeature* find_gpu(int device_id) const;

    /**
     * @brief Find NVMe device by path
     * @param device_path Device path (e.g., "/dev/nvme0")
     * @return Pointer to NvmeFeature or nullptr if not found
     */
    const NvmeFeature* find_nvme(const string& device_path) const;

    /**
     * @brief Get list of GPUs with FULL P2P support
     * @return Vector of indices into gpus vector
     */
    std::vector<size_t> get_p2p_capable_gpus() const;

    /**
     * @brief Get list of NVMe devices with FULL P2P support
     * @return Vector of indices into nvme_devs vector
     */
    std::vector<size_t> get_p2p_capable_nvme() const;

    /**
     * @brief Select devices based on requirements
     * @param req Device requirements
     * @param enable_log Enable logging to stderr (default: true)
     * @return Selected devices (pointers may be nullptr if not found)
     *
     * Selection algorithm:
     * 1. Filter devices by requirements
     * 2. Sort by memory/capacity (descending)
     * 3. Return highest-memory/capacity device
     *
     * Failure reasons are always captured in result logs.
     * If enable_log=true, also prints to stderr.
     */
    SelectedDevices select_devices(const DeviceRequirements& req, bool enable_log = true) const;

    /**
     * @brief Select devices for P2P DMA tests
     * @return Best P2P-capable GPU and NVMe
     */
    SelectedDevices select_for_p2p() const {
        return select_devices(DeviceRequirements::for_p2p());
    }

    /**
     * @brief Select devices for host DMA tests
     * @return Best NVMe for host-initiated I/O
     */
    SelectedDevices select_for_host_dma() const {
        return select_devices(DeviceRequirements::for_host_dma());
    }

    /**
     * @brief Select devices for GPU compute tests
     * @return Best GPU for compute
     */
    SelectedDevices select_for_gpu_compute() const {
        return select_devices(DeviceRequirements::for_gpu_compute());
    }

    /**
     * @brief Select devices for shadow doorbell tests
     * @return Best NVMe with shadow doorbell support
     */
    SelectedDevices select_for_shadow_doorbell() const {
        return select_devices(DeviceRequirements::for_shadow_doorbell());
    }

    /**
     * @brief Get all GPUs matching requirements, sorted by memory
     * @param req Requirements to match
     * @return Vector of GPU indices (into gpus vector)
     */
    std::vector<size_t> get_matching_gpus(const DeviceRequirements& req) const;

    /**
     * @brief Get all NVMe devices matching requirements, sorted by capacity
     * @param req Requirements to match
     * @return Vector of NVMe indices (into nvme_devs vector)
     */
    std::vector<size_t> get_matching_nvme(const DeviceRequirements& req) const;

    /**
     * @brief Detect all devices in the system
     * @return Complete system feature information
     *
     * This static method performs comprehensive device detection:
     * 1. Detects host system capabilities (IOMMU, VFIO, kernel modules)
     * 2. Enumerates all CUDA GPUs and their features
     * 3. Enumerates all NVMe devices and their features
     * 4. Cross-references P2P compatibility
     *
     * @code
     * auto features = SystemFeatures::detect_all();
     *
     * printf("System Summary:\n%s\n", features.get_summary().c_str());
     *
     * if (features.is_p2p_ready()) {
     *     printf("System is ready for GPU-NVMe P2P!\n");
     * } else {
     *     printf("P2P not fully supported. Check individual features:\n");
     *     features.print_all(true);
     * }
     * @endcode
     */
    static SystemFeatures detect_all();

private:
    /**
     * @brief Check if GPU matches requirements
     * @param gpu GPU to check
     * @param req Requirements to match against
     * @return true if GPU meets all requirements
     */
    bool gpu_matches(const GpuFeature& gpu, const DeviceRequirements& req) const;

    /**
     * @brief Check if NVMe device matches requirements
     * @param nvme NVMe device to check
     * @param req Requirements to match against
     * @return true if NVMe meets all requirements
     */
    bool nvme_matches(const NvmeFeature& nvme, const DeviceRequirements& req) const;

    /**
     * @brief Check if host matches requirements
     * @param host_feat Host to check
     * @param req Requirements to match against
     * @return true if host meets all requirements
     */
    bool host_matches(const HostFeature& host_feat, const DeviceRequirements& req) const;
};

/**
 * @brief Detect all devices in the system (deprecated, use SystemFeatures::detect_all())
 * @return Complete system feature information
 * @deprecated Use SystemFeatures::detect_all() instead
 */
[[deprecated("Use SystemFeatures::detect_all() instead")]]
inline SystemFeatures detect_all_devices() {
    return SystemFeatures::detect_all();
}

/**
 * @brief Print system compatibility report
 * @param features System features to analyze
 *
 * Prints detailed report showing:
 * - What is working
 * - What is missing
 * - How to fix issues
 */
void print_compatibility_report(const SystemFeatures& features);
