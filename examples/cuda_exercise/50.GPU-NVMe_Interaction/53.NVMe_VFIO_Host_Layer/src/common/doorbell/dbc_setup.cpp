/**
 * @file dbc_setup.cpp
 * @brief Implementation of DBC setup utilities
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-20
 */

#include "dbc_setup.h"
#include <cstdlib>
#include <cstring>
#include <cstdio>
#include <sys/ioctl.h>
#include <linux/nvme_ioctl.h>

// External functions from host layer
extern "C" {
    int host_map_iova(void* ptr, size_t size, uint64_t* iova);
    void host_unmap_iova(void* ptr, size_t size, uint64_t iova);
}

namespace nvme {

ShadowDoorbellBuffer* allocate_shadow_doorbell_buffer(
    uint16_t queue_count,
    size_t page_size) {

    const size_t bytes = calculate_dbc_buffer_size(queue_count);

    // Allocate page-aligned memory
    void* raw = nullptr;
    if (posix_memalign(&raw, page_size, bytes) != 0) {
        fprintf(stderr, "[DBC] ERROR: posix_memalign failed for %zu bytes\n", bytes);
        return nullptr;
    }

    // Clear the buffer
    std::memset(raw, 0, bytes);

    // Map for DMA access
    uint64_t iova = 0;
    if (host_map_iova(raw, bytes, &iova) != 0) {
        fprintf(stderr, "[DBC] ERROR: host_map_iova failed\n");
        free(raw);
        return nullptr;
    }

    // Create buffer descriptor
    auto* buffer = new ShadowDoorbellBuffer();
    buffer->host_ptr = static_cast<uint32_t*>(raw);
    buffer->bytes = bytes;
    buffer->iova = iova;
    buffer->queue_count = queue_count;

    return buffer;
}

void free_shadow_doorbell_buffer(ShadowDoorbellBuffer* buffer) {
    if (!buffer) {
        return;
    }

    // Unmap IOVA - must use page-aligned size to match what was mapped
    if (buffer->host_ptr && buffer->bytes && buffer->iova) {
        // Round up to page size (typically 4096) to match what host_map_iova did
        size_t page_size = 4096;  // Standard page size
        size_t aligned_bytes = (buffer->bytes + page_size - 1) & ~(page_size - 1);
        host_unmap_iova(buffer->host_ptr, aligned_bytes, buffer->iova);
    }

    // Free memory
    if (buffer->host_ptr) {
        free(buffer->host_ptr);
    }

    delete buffer;
}

int nvme_configure_hardware_dbc(int device_fd,
                                 const ShadowDoorbellBuffer* buffer,
                                 uint16_t queue_count,
                                 bool enable_event_idx) {
    if (device_fd < 0 || !buffer || !buffer->host_ptr || buffer->iova == 0) {
        fprintf(stderr, "[DBC] ERROR: Invalid parameters for DBC configuration\n");
        return -1;
    }

    // Prepare NVMe Admin Command 0x7C (Doorbell Buffer Config)
    struct nvme_admin_cmd cmd = {};

    cmd.opcode = 0x7C;  // Doorbell Buffer Config command
    cmd.nsid = 0;       // Not namespace-specific
    cmd.addr = 0;       // No data transfer
    cmd.data_len = 0;

    // CDW10: Doorbell count and event index enable
    // Bits [15:0]: Number of doorbells (queue_count * 2 for SQ + CQ)
    // Bit [16]: Event Index Enable (0=disabled, 1=enabled)
    uint32_t doorbell_count = queue_count * 2;
    uint32_t cdw10 = doorbell_count | (enable_event_idx ? (1 << 16) : 0);
    cmd.cdw10 = cdw10;

    // CDW11: Shadow doorbell buffer IOVA (low 32 bits)
    cmd.cdw11 = static_cast<uint32_t>(buffer->iova & 0xFFFFFFFF);

    // CDW12: Shadow doorbell buffer IOVA (high 32 bits)
    cmd.cdw12 = static_cast<uint32_t>(buffer->iova >> 32);

    // Send admin command via ioctl
    int ret = ioctl(device_fd, NVME_IOCTL_ADMIN_CMD, &cmd);

    if (ret != 0) {
        fprintf(stderr, "[DBC] ERROR: Failed to configure hardware DBC (ioctl returned %d)\n", ret);
        fprintf(stderr, "[DBC]   Device FD: %d\n", device_fd);
        fprintf(stderr, "[DBC]   IOVA: 0x%lx\n", buffer->iova);
        fprintf(stderr, "[DBC]   Doorbell count: %u\n", doorbell_count);
        fprintf(stderr, "[DBC]   Event index: %s\n", enable_event_idx ? "enabled" : "disabled");
        return ret;
    }

    fprintf(stderr, "[DBC] SUCCESS: Hardware DBC configured\n");
    fprintf(stderr, "[DBC]   Shadow buffer IOVA: 0x%lx\n", buffer->iova);
    fprintf(stderr, "[DBC]   Doorbell count: %u (%u queues)\n", doorbell_count, queue_count);
    fprintf(stderr, "[DBC]   Event index: %s\n", enable_event_idx ? "enabled" : "disabled");

    return 0;
}

}  // namespace nvme