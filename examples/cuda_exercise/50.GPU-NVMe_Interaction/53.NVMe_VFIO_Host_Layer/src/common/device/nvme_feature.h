/**
 * @file nvme_feature.h
 * @brief NVMe device feature detection and capabilities
 *
 * Detects NVMe devices and reports:
 * - Number of namespaces
 * - Queue count (submission/completion)
 * - Shadow doorbell buffer support
 * - P2P DMA support
 * - Performance characteristics
 */

#pragma once
#include "feature.h"
#include "cuda_utils.h"
#include <vector>

/**
 * @brief NVMe device features and capabilities
 *
 * Represents a single NVMe device (e.g., /dev/nvme0) and its capabilities.
 * Use get_all_nvme_devices() to enumerate all available NVMe devices.
 */
class NvmeFeature : public Feature {
public:
    /**
     * @brief Construct NVMe feature detector for specific device
     * @param device_path Device path (e.g., "/dev/nvme0")
     */
    explicit NvmeFeature(const string& device_path);

    // Feature interface
    bool is_available() const override { return available_; }
    string get_name() const override;
    string get_description() const override;
    void print(bool verbose = false) const override;

    // NVMe-specific queries

    /**
     * @brief Get device path (e.g., "/dev/nvme0")
     */
    string get_device_path() const { return device_path_; }

    /**
     * @brief Get PCI bus ID (e.g., "0000:08:00.0")
     */
    string get_pci_bus_id() const { return pci_bus_id_; }

    /**
     * @brief Get number of active namespaces
     */
    uint32_t get_num_namespaces() const { return num_namespaces_; }

    /**
     * @brief Get maximum number of I/O submission queues supported
     */
    uint32_t get_max_io_queues() const { return max_io_queues_; }

    /**
     * @brief Get maximum queue depth (entries per queue)
     */
    uint32_t get_max_queue_depth() const { return max_queue_depth_; }

    /**
     * @brief Check if shadow doorbell buffer is supported
     * @return Support level for shadow doorbell feature
     *
     * Shadow doorbell allows reducing MMIO writes by batching doorbell updates.
     */
    SupportLevel get_shadow_doorbell_support() const { return shadow_doorbell_support_; }

    /**
     * @brief Check if device supports P2P DMA with GPUs
     * @return Support level for GPU P2P DMA
     *
     * @note FULL support requires:
     *   - Device in IOMMU group
     *   - VFIO-PCI driver bound
     *   - gpu_p2p_nvme kernel module loaded
     */
    SupportLevel get_p2p_support() const { return p2p_support_; }

    /**
     * @brief Get device capacity in bytes
     */
    uint64_t get_capacity_bytes() const { return capacity_bytes_; }

    /**
     * @brief Get namespace LBA size in bytes (typically 512 or 4096)
     * @param nsid Namespace ID (1-based)
     */
    uint32_t get_lba_size(uint32_t nsid = 1) const;

    /**
     * @brief Check if VFIO-PCI driver is bound to device
     */
    bool has_vfio_binding() const { return vfio_bound_; }

    /**
     * @brief Get controller model name
     */
    string get_model() const { return model_; }

    /**
     * @brief Get firmware version
     */
    string get_firmware_version() const { return firmware_version_; }

    /**
     * @brief Get NVMe specification version (major)
     * @return Major version number (e.g., 1 for NVMe 1.4)
     */
    uint8_t get_nvme_version_major() const { return nvme_version_major_; }

    /**
     * @brief Get NVMe specification version (minor)
     * @return Minor version number (e.g., 4 for NVMe 1.4)
     */
    uint8_t get_nvme_version_minor() const { return nvme_version_minor_; }

    /**
     * @brief Get OACS (Optional Admin Command Support) field value
     * @return 16-bit OACS value from Identify Controller (bit 8 = DBC support)
     */
    uint16_t get_oacs() const { return oacs_; }

    /**
     * @brief Check if device has filesystem or partitions
     * @return true if device has partition table or mounted filesystem
     *
     * SAFETY: Prevents accidental testing on devices with data.
     * Checks:
     * - Mounted filesystems (/proc/mounts)
     * - Partition table presence (fdisk -l)
     * - Root device detection (/proc/cmdline)
     */
    bool is_filesystem_bound() const { return has_filesystem_; }

    /**
     * @brief Check if device is boot device
     * @return true if device contains root filesystem or /boot
     *
     * CRITICAL SAFETY: Prevents testing on system boot drive.
     */
    bool is_boot_device() const { return is_boot_device_; }

    /**
     * @brief Check if device is actively used by the OS
     * @return true if the device has filesystems or is the boot/root device
     *
     * Convenience helper used by tests/choosers to avoid touching OS-critical
     * NVMe drives. Equivalent to `is_filesystem_bound() || is_boot_device()`.
     */
    bool is_os_live() const { return has_filesystem_ || is_boot_device_; }

    /**
     * @brief Validate LBA range is safe for testing
     * @param start_lba Starting LBA
     * @param num_lbas Number of LBAs
     * @param min_safe_offset_gb Minimum offset from start in GB (default: 100GB)
     * @return true if range is safe (within capacity, beyond offset)
     *
     * SAFETY: Ensures test range doesn't overlap with critical data areas.
     */
    bool is_lba_range_safe(uint64_t start_lba, uint64_t num_lbas,
                          uint32_t min_safe_offset_gb = 100) const;

private:
    void detect_features();
    void detect_vfio_status();
    void detect_shadow_doorbell();
    void read_identify_controller();
    void detect_filesystem_status();  // New: Check for filesystems/partitions
    void detect_boot_device_status(); // New: Check if boot device

    string device_path_;
    string pci_bus_id_;
    string model_;
    string firmware_version_;
    bool available_{false};
    bool vfio_bound_{false};
    bool has_filesystem_{false};      // New: Has filesystem or partitions
    bool is_boot_device_{false};      // New: Is boot/root device
    uint32_t num_namespaces_{0};
    uint32_t max_io_queues_{0};
    uint32_t max_queue_depth_{0};
    uint64_t capacity_bytes_{0};
    uint32_t lba_size_{512};  // Default
    uint8_t nvme_version_major_{0};   // NVMe spec major version
    uint8_t nvme_version_minor_{0};   // NVMe spec minor version
    uint16_t oacs_{0};                // Optional Admin Command Support
    SupportLevel shadow_doorbell_support_{SupportLevel::NOT_SUPPORTED};
    SupportLevel p2p_support_{SupportLevel::NOT_SUPPORTED};
};

/**
 * @brief Enumerate all available NVMe devices
 * @return Vector of NvmeFeature objects for each detected device
 *
 * Scans /dev/nvme* and /sys/class/nvme/ for devices.
 *
 * @code
 * auto nvme_devs = get_all_nvme_devices();
 * for (const auto& dev : nvme_devs) {
 *     dev.print(true);  // Print detailed info
 * }
 * @endcode
 */
std::vector<NvmeFeature> get_all_nvme_devices();
