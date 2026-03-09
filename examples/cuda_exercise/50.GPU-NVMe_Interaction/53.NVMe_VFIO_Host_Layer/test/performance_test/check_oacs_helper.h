/**
 * @file check_oacs_helper.h
 * @brief Helper to check OACS value through existing NVMe device handle
 */

#pragma once

#include <cstdint>
#include <cstring>
#include "mapper/mapper_host.h"

namespace perf_test {

/**
 * @brief Check OACS (Optional Admin Command Support) value from device
 *
 * @param dev NVMe device handle (from nvme_open)
 * @param[out] oacs The OACS value (if successful)
 * @return true if successfully retrieved OACS, false otherwise
 */
inline bool get_device_oacs(NvmeDevice* dev, uint16_t* oacs) {
    if (!dev || !oacs) return false;

    // Prepare buffer for identify controller data
    uint8_t* id_ctrl = (uint8_t*)aligned_alloc(4096, 4096);
    if (!id_ctrl) return false;

    memset(id_ctrl, 0, 4096);

    // Build Identify Controller command
    NvmeCmd cmd{};
    cmd.opc = 0x06;  // OPC_ADMIN_IDENTIFY
    cmd.nsid = 0;
    cmd.cdw10 = 1;   // Controller identify (CNS=1)

    // Map buffer for DMA
    uint64_t iova = nvme_map_prp(dev, id_ctrl, 4096);
    if (!iova) {
        free(id_ctrl);
        return false;
    }

    cmd.prp1 = iova;

    // Submit command to admin queue
    uint16_t cid = nvme_admin_submit_cmd(dev, &cmd);

    // Poll for completion
    NvmeStatus status = nvme_admin_poll_cmd(dev, cid);

    bool success = false;
    if (!status.is_error()) {
        // Extract OACS at byte offset 256
        *oacs = *(uint16_t*)(id_ctrl + 256);

        // Also extract and print version and model for debugging
        uint32_t vs = *(uint32_t*)(id_ctrl + 8);
        uint8_t major = (vs >> 16) & 0xFF;
        uint8_t minor = (vs >> 8) & 0xFF;

        char model[41] = {0};
        memcpy(model, id_ctrl + 24, 40);
        // Trim trailing spaces
        for (int i = 39; i >= 0; i--) {
            if (model[i] == ' ' || model[i] == '\0') {
                model[i] = '\0';
            } else {
                break;
            }
        }

        printf("\n========================================\n");
        printf("NVMe Controller Information:\n");
        printf("  Model: %s\n", model);
        printf("  NVMe Version: %d.%d\n", major, minor);
        printf("  OACS Value: 0x%04x\n", *oacs);
        printf("  OACS Bits:\n");

        if (*oacs & (1 << 0)) printf("    Bit 0: Security Send/Receive\n");
        if (*oacs & (1 << 1)) printf("    Bit 1: Format NVM\n");
        if (*oacs & (1 << 2)) printf("    Bit 2: Firmware Download/Commit\n");
        if (*oacs & (1 << 3)) printf("    Bit 3: Namespace Management\n");
        if (*oacs & (1 << 4)) printf("    Bit 4: Device Self-test\n");
        if (*oacs & (1 << 5)) printf("    Bit 5: Directives\n");
        if (*oacs & (1 << 6)) printf("    Bit 6: NVMe-MI Send/Receive\n");
        if (*oacs & (1 << 7)) printf("    Bit 7: Virtualization Management\n");
        if (*oacs & (1 << 8)) printf("    Bit 8: Doorbell Buffer Config (DBC) *** SUPPORTED ***\n");
        else printf("    Bit 8: Doorbell Buffer Config (DBC) - NOT SUPPORTED\n");
        if (*oacs & (1 << 9)) printf("    Bit 9: Get LBA Status\n");

        printf("========================================\n\n");

        success = true;
    } else {
        printf("Failed to get Identify Controller data (status=%d)\n", status.raw);
    }

    // Unmap and free buffer
    nvme_unmap_prp(dev, id_ctrl, 4096, iova);
    free(id_ctrl);

    return success;
}

/**
 * @brief Check if device supports DBC (Doorbell Buffer Config)
 *
 * @param dev NVMe device handle
 * @return true if DBC is supported (OACS bit 8), false otherwise
 */
inline bool check_dbc_support(NvmeDevice* dev) {
    uint16_t oacs = 0;
    if (get_device_oacs(dev, &oacs)) {
        bool dbc_supported = (oacs & (1 << 8)) != 0;
        if (dbc_supported) {
            printf("✓ DBC Support DETECTED (OACS bit 8 is set)\n");
        } else {
            printf("✗ DBC Support NOT AVAILABLE (OACS bit 8 is not set)\n");
        }
        return dbc_supported;
    }
    printf("✗ Failed to check DBC support\n");
    return false;
}

} // namespace perf_test