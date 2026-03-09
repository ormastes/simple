/**
 * @file dbc_setup.h
 * @brief DBC (Doorbell Buffer Config) setup utilities
 */

#pragma once

#include <cstdint>
#include <cstddef>

namespace nvme {

/**
 * @brief Shadow doorbell buffer for DBC
 */
struct ShadowDoorbellBuffer {
    uint32_t* host_ptr{nullptr};    ///< Host memory pointer
    size_t bytes{0};                 ///< Buffer size in bytes
    uint64_t iova{0};                ///< IO Virtual Address for DMA
    uint16_t queue_count{1};         ///< Number of queues supported
};

/**
 * @brief Allocate shadow doorbell buffer for DBC
 * @param queue_count Number of queues
 * @param page_size Page size
 * @return Allocated buffer or nullptr
 */
ShadowDoorbellBuffer* allocate_shadow_doorbell_buffer(
    uint16_t queue_count,
    size_t page_size);

/**
 * @brief Free shadow doorbell buffer
 * @param buffer Buffer to free
 */
void free_shadow_doorbell_buffer(ShadowDoorbellBuffer* buffer);

/**
 * @brief Configure hardware DBC (Doorbell Buffer Config) on NVMe controller
 *
 * Sends NVMe Admin Command 0x7C to enable hardware shadow doorbell polling.
 * The controller will poll the shadow buffer via DMA instead of requiring
 * MMIO writes for each doorbell ring.
 *
 * @param device_fd VFIO device file descriptor
 * @param buffer Shadow doorbell buffer (must be allocated and mapped)
 * @param queue_count Number of I/O queues (determines doorbell count)
 * @param enable_event_idx Enable event index for interrupt moderation
 * @return 0 on success, negative error code on failure
 *
 * @note Requires NVMe controller with OACS bit 8 set (DBC support)
 * @note Must be called after queue creation but before I/O operations
 */
int nvme_configure_hardware_dbc(int device_fd,
                                 const ShadowDoorbellBuffer* buffer,
                                 uint16_t queue_count,
                                 bool enable_event_idx = false);

/**
 * @brief DBC configuration parameters
 */
struct DbcConfig {
    uint16_t queue_count{1};         ///< Number of queues
    bool use_event_idx{false};       ///< Enable event index (interrupt moderation)
    uint32_t poll_interval_us{10};   ///< Polling interval for daemon mode (microseconds)
};

/**
 * @brief Calculate required buffer size for DBC
 * @param queue_count Number of queues
 * @return Buffer size in bytes
 */
inline size_t calculate_dbc_buffer_size(uint16_t queue_count) {
    // NVMe spec: 2 doorbells (SQ+CQ) per queue, 4 bytes each
    return static_cast<size_t>(queue_count) * 2 * sizeof(uint32_t);
}

/**
 * @brief Get doorbell offset for specific queue
 * @param qid Queue ID
 * @param is_cq true for CQ, false for SQ
 * @return Byte offset
 */
inline size_t get_doorbell_offset(uint16_t qid, bool is_cq) {
    // NVMe spec: SQ at index 2*qid, CQ at index 2*qid+1
    return (2 * qid + (is_cq ? 1 : 0)) * sizeof(uint32_t);
}

}  // namespace nvme