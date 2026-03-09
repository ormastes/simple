/**
 * @file host_feature.h
 * @brief Host system feature detection and capabilities
 *
 * Detects host system capabilities:
 * - VFIO support (hardware and software)
 * - IOMMU status
 * - Kernel module support
 * - P2P DMA infrastructure
 * - OS version and configuration
 */

#pragma once
#include "feature.h"
#include "cuda_utils.h"

/**
 * @brief Host system features and capabilities
 *
 * Represents the host system's support for NVMe and GPU features.
 * This is a singleton - use get_host_features() to access.
 */
class HostFeature : public Feature {
public:
    /**
     * @brief Construct host feature detector
     */
    HostFeature();

    // Feature interface
    bool is_available() const override { return true; }  // Host is always "available"
    string get_name() const override;
    string get_description() const override;
    void print(bool verbose = false) const override;

    // Host-specific queries

    /**
     * @brief Check if hardware supports IOMMU
     * @return true if CPU and motherboard have IOMMU support (VT-d/AMD-Vi)
     */
    bool has_iommu_hardware() const { return iommu_hardware_; }

    /**
     * @brief Check if IOMMU is enabled in kernel
     * @return true if iommu=on or intel_iommu=on kernel parameter is set
     */
    bool has_iommu_enabled() const { return iommu_enabled_; }

    /**
     * @brief Get VFIO support level
     * @return Support level for VFIO framework
     *
     * Requirements for FULL support:
     * - IOMMU hardware present
     * - IOMMU enabled in kernel
     * - vfio and vfio-pci modules loaded
     * - /dev/vfio/vfio accessible
     */
    SupportLevel get_vfio_support() const { return vfio_support_; }

    /**
     * @brief Get P2P DMA support level
     * @return Support level for GPU-NVMe P2P
     *
     * Requirements for FULL support:
     * - VFIO support (FULL)
     * - gpu_p2p_nvme kernel module loaded
     * - ACS override enabled (if needed)
     */
    SupportLevel get_p2p_support() const { return p2p_support_; }

    /**
     * @brief Check if VFIO kernel module is loaded
     */
    bool has_vfio_module() const { return vfio_module_loaded_; }

    /**
     * @brief Check if gpu_p2p_nvme kernel module is loaded
     */
    bool has_p2p_module() const { return p2p_module_loaded_; }

    /**
     * @brief Check if ACS override is enabled
     * @return true if ACS is disabled (P2P possible)
     *
     * ACS (Access Control Services) can block P2P between devices.
     * This checks BOTH:
     * 1. Kernel parameter (pci=noacs or pcie_acs_override) - user intent
     * 2. Actual PCIe ACS state by reading config space - verified state
     *
     * Returns true if EITHER the kernel parameter is set OR actual ACS
     * control registers show ACS is disabled on PCIe devices.
     *
     * Note: Reading PCIe config space requires read access to sysfs
     * (/sys/bus/pci/devices/<BDF>/config) available without root on most systems
     */
    bool has_acs_override() const { return acs_override_; }

    /**
     * @brief Get kernel version string
     */
    string get_kernel_version() const { return kernel_version_; }

    /**
     * @brief Get OS distribution name
     */
    string get_os_name() const { return os_name_; }

    /**
     * @brief Get total system memory in bytes
     */
    uint64_t get_total_memory() const { return total_memory_bytes_; }

    /**
     * @brief Check if running as root or with CAP_SYS_ADMIN
     */
    bool has_admin_privileges() const { return has_admin_; }

    /**
     * @brief Get number of IOMMU groups
     * @return Count of /sys/kernel/iommu_groups/* entries
     */
    uint32_t get_iommu_group_count() const { return iommu_group_count_; }

private:
    void detect_iommu();
    void detect_vfio();
    void detect_p2p();
    void detect_kernel_info();
    void detect_os_info();
    void detect_memory();
    void detect_privileges();
    bool check_acs_state_for_device(const string& bdf);

    bool iommu_hardware_{false};
    bool iommu_enabled_{false};
    bool vfio_module_loaded_{false};
    bool p2p_module_loaded_{false};
    bool acs_override_{false};
    bool has_admin_{false};
    uint32_t iommu_group_count_{0};
    uint64_t total_memory_bytes_{0};
    SupportLevel vfio_support_{SupportLevel::NOT_SUPPORTED};
    SupportLevel p2p_support_{SupportLevel::NOT_SUPPORTED};
    string kernel_version_;
    string os_name_;
};

/**
 * @brief Get host features (singleton)
 * @return Reference to host feature detector
 *
 * @code
 * const auto& host = get_host_features();
 * if (host.get_vfio_support() == SupportLevel::FULL) {
 *     printf("VFIO is fully supported!\n");
 * }
 * @endcode
 */
const HostFeature& get_host_features();
