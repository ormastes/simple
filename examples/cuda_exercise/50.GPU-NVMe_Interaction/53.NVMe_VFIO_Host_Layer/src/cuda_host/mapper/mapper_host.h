/**
 * @file mapper_host.h
 * @brief Host-side NVMe memory mapper APIs for VFIO-based device access
 *
 * Provides device initialization, queue setup, and device property access.
 * Contains C API for backward compatibility and foundation for unified mapper interface.
 */

#pragma once
#include <cstdint>
#include <cstddef>
#include "nvme_types.h"        // For NvmeCmd, NvmeCqe, PollResult, etc.
#include "queue/nvme_queue.h"        // For NvmeQueue, DoorbellMode (merged header)
#include "doorbell/nvme_doorbell.h"
#include "memory/memory_types.h"     // For ItemSize
#include "forward_decls.h"

// ============================================================================
// NVMe Register Offsets
// ============================================================================

/**
 * @brief NVMe controller register offsets (NVMe 1.4 spec, Section 3)
 */
namespace nvme_reg {
    static constexpr uint32_t CAP           = 0x0000;  ///< Controller Capabilities
    static constexpr uint32_t VS            = 0x0008;  ///< Version
    static constexpr uint32_t CC            = 0x0014;  ///< Controller Configuration
    static constexpr uint32_t CSTS          = 0x001c;  ///< Controller Status
    static constexpr uint32_t AQA           = 0x0024;  ///< Admin Queue Attributes
    static constexpr uint32_t ASQ           = 0x0028;  ///< Admin Submission Queue Base
    static constexpr uint32_t ACQ           = 0x0030;  ///< Admin Completion Queue Base
    static constexpr uint32_t DOORBELL_BASE = 0x1000;  ///< Doorbell register base offset
}

// ============================================================================
// Legacy Queue Structure (DEPRECATED)
// ============================================================================

/**
 * @brief Legacy queue descriptor (host-side only)
 * @deprecated Use NvmeQueue from nvme_queue_struct.h instead
 */
struct Queue {
    void*                        vaddr{nullptr};         ///< Virtual address of queue memory
    uint64_t                iova{0};                ///< IOVA address for DMA mapping
    uint16_t                entries{0};             ///< Queue depth (number of entries)
    uint16_t                head{0};                ///< Queue head index
    uint16_t                tail{0};                ///< Queue tail index
    uint16_t                qid{0};                 ///< Queue ID
    uint8_t                 phase{1};               ///< Phase bit (0 or 1)
    size_t                  entry_size{0};          ///< Size of each queue entry
    volatile uint32_t*      db{nullptr};            ///< Doorbell register pointer

    // Command pools for performance optimization (populated by nvme_setup_host_queue)
    NvmeCmd*                     read_cmd_pool{nullptr}; ///< Pre-built READ commands
    NvmeCmd*                     write_cmd_pool{nullptr};///< Pre-built WRITE commands
};

// ============================================================================
// Opaque Device Handle (defined in forward_decls.h)
// ============================================================================

// ============================================================================
// Host-Side NVMe Device APIs
// ============================================================================

extern "C" {

// ============================================================================
// Enhanced API for Page Size Configuration Support
// ============================================================================

/**
 * @brief Initialize NVMe device without enabling controller (allows page size configuration)
 * @param bdf PCI BDF string (e.g., "0000:01:00.0")
 * @param item_size_bytes Desired transfer size in bytes
 * @return NvmeDevice handle on success, nullptr on failure
 * @note Controller remains disabled - call nvme_enable() after configuration
 */
NvmeDevice* nvme_init(const char* bdf, uint32_t item_size_bytes);

/**
 * @brief Enable NVMe controller with configured settings
 * @param d NVMe device handle (from nvme_init())
 * @param admin_qd Admin queue depth
 * @param io_qd I/O queue depth
 * @return true on success, false on failure
 * @note Creates admin and I/O queues, device ready for operations
 */
bool nvme_enable(NvmeDevice* d, uint16_t admin_qd, uint16_t io_qd);

// ============================================================================
// Legacy API (Backward Compatibility)
// ============================================================================

/**
 * @brief Open NVMe device via VFIO and initialize queues (legacy API)
 * @param bdf PCI BDF string (e.g., "0000:01:00.0")
 * @param admin_qd Admin queue depth
 * @param io_qd I/O queue depth
 * @param item_size_bytes Desired transfer size in bytes
 * @return NvmeDevice handle on success, nullptr on failure
 * @note Device selects largest LBA size that divides item_size_bytes
 * @note Uses nvme_init() + nvme_enable() internally for compatibility
 */
NvmeDevice* nvme_open(const char* bdf, uint16_t admin_qd, uint16_t io_qd, uint32_t item_size_bytes);

/**
 * @brief Close NVMe device and cleanup resources
 *
 * @param d NVMe device handle (from nvme_open() or nvme_init())
 */
void nvme_close(NvmeDevice* d);

/**
 * @brief Get I/O submission queue (legacy API)
 *
 * @deprecated Use nvme_setup_host_queue() to get NvmeQueue instead
 * @param d NVMe device handle
 * @return Legacy Queue pointer (QID 1)
 */
Queue* nvme_get_iosq(NvmeDevice* d);

/**
 * @brief Get I/O completion queue (legacy API)
 *
 * @deprecated Use nvme_setup_host_queue() to get NvmeQueue instead
 * @param d NVMe device handle
 * @return Legacy Queue pointer (QID 1)
 */
Queue* nvme_get_iocq(NvmeDevice* d);

/**
 * @brief Get device page size for PRP list construction
 * @param d NVMe device handle
 * @return Page size in bytes (typically 4096)
 */
size_t nvme_get_page_size(NvmeDevice* d);

/**
 * @brief Get maximum supported page size
 *
 * @param d NVMe device handle
 * @return Maximum page size in bytes
 */
size_t nvme_get_max_page_size(NvmeDevice* d);

/**
 * @brief Set controller page size (enhanced API - works with nvme_init/nvme_enable flow)
 *
 * @param d NVMe device handle (from nvme_init(), before nvme_enable())
 * @param page_size Desired page size in bytes (must be power of 2, >= 4KB)
 * @return true if page size is supported and set successfully, false otherwise
 * @note Must be called after nvme_init() and before nvme_enable()
 */
bool nvme_set_page_size(NvmeDevice* d, size_t page_size);

/**
 * @brief Get array of all supported page sizes
 *
 * @param d NVMe device handle
 * @param array_size Output parameter: number of supported page sizes
 * @return Pointer to array of supported page sizes in bytes (caller must free)
 */
size_t* nvme_available_sizes(NvmeDevice* d, size_t* array_size);

/**
 * @brief Get LBA size selected during nvme_open()
 * @param d NVMe device handle
 * @return LBA size in bytes (512, 4096, etc.)
 */
uint32_t nvme_get_lba_size(NvmeDevice* d);

/**
 * @brief Get item size descriptor configured during nvme_open()
 * @param d NVMe device handle
 * @return ItemSize structure with LBA size, count, and total transfer size
 */
ItemSize nvme_get_item_size(NvmeDevice* d);

/**
 * @brief Get supported doorbell mode
 *
 * @param d NVMe device handle
 * @return Supported doorbell mode (highest capability)
 */
DoorbellMode nvme_get_support_doorbell(NvmeDevice* d);

/**
 * @brief Get device file descriptor for direct ioctl access
 *
 * @param d NVMe device handle
 * @return VFIO device file descriptor, or -1 if invalid
 * @note Use with caution - direct ioctl bypasses internal state management
 */
int nvme_get_device_fd(NvmeDevice* d);

// ============================================================================
// Host Queue Setup
// ============================================================================

/**
 * @brief Setup NVMe queue descriptor from existing device queues
 * @param nvme_dev NVMe device handle (from nvme_open())
 * @param nvme_bdf NVMe PCI BDF string (unused for host, kept for API consistency)
 * @param out_queue Output queue descriptor
 * @return 0 on success, -1 on failure
 */
int nvme_setup_host_queue(NvmeDevice* nvme_dev,
                          const char* nvme_bdf,
                          NvmeQueueStruct* out_queue);

/**
 * @brief Cleanup host queue and free command pools
 * @param queue Queue descriptor with command pools to free
 */
void nvme_cleanup_host_queue(NvmeQueueStruct* queue);

// ============================================================================
// Internal IOVA Mapping Functions (Implementation Detail)
// ============================================================================

/**
 * @brief Map host memory to IOVA address space (internal use)
 * @internal Use Mapper interface instead of calling directly
 * @param host Virtual address to map
 * @param bytes Size in bytes
 * @param[out] out_iova Output IOVA address
 * @return 0 on success, -1 on failure
 */
int host_map_iova(void* host, size_t bytes, uint64_t* out_iova);

/**
 * @brief Unmap host memory from IOVA address space (internal use)
 * @internal Use Mapper interface instead of calling directly
 * @param host Virtual address
 * @param bytes Size in bytes
 * @param iova IOVA address to unmap
 * @return 0 on success, -1 on failure
 */
int host_unmap_iova(void* host, size_t bytes, uint64_t iova);

} // extern "C"
