/*
 * Independent C oracle frozen from the pre-migration cosmos_pcie.c policy.
 * It intentionally includes neither the migrated header nor production
 * register headers: constants and expressions below are an independent copy.
 */
#include "cosmos_pcie_residual_policy_oracle.h"

#define ORACLE_OK 0
#define ORACLE_UNAVAILABLE 1
#define ORACLE_INVALID 2
#define ORACLE_HW_ERROR 4

int cosmos_pcie_residual_oracle_snapshot_status(
    unsigned int status, unsigned int function,
    unsigned int nvme, unsigned int admin) {
    const unsigned int admin_valid = admin & 0x3U;

    if ((status & ~0x0000013FU) != 0U ||
        (function & ~0x0000007FU) != 0U ||
        (nvme & ~0x00000077U) != 0U ||
        (admin & ~0x00000007U) != 0U) {
        return ORACLE_HW_ERROR;
    }
    if ((status & 0x100U) == 0U ||
        (status & 0x3FU) != 0x16U ||
        (function & 0x1U) == 0U ||
        (function & 0x2U) == 0U) {
        return ORACLE_UNAVAILABLE;
    }
    if ((function & 0x4U) != 0U ||
        ((function & 0x70U) >> 4U) > 3U) {
        return ORACLE_HW_ERROR;
    }
    if (admin_valid != 0U && admin_valid != 0x3U) {
        return ORACLE_HW_ERROR;
    }
    if ((admin & 0x4U) != 0U && (admin & 0x1U) == 0U) {
        return ORACLE_HW_ERROR;
    }
    if ((nvme & 0x1U) == 0U &&
        ((nvme & 0x76U) != 0U || admin != 0U)) {
        return ORACLE_HW_ERROR;
    }
    if ((nvme & 0x10U) != 0U && (admin & 0x7U) != 0x7U) {
        return ORACLE_HW_ERROR;
    }
    return ORACLE_OK;
}

int cosmos_pcie_residual_oracle_snapshots_equal(
    unsigned int left_status, unsigned int left_function,
    unsigned int left_nvme, unsigned int left_admin,
    unsigned int right_status, unsigned int right_function,
    unsigned int right_nvme, unsigned int right_admin) {
    return left_status == right_status &&
        left_function == right_function &&
        left_nvme == right_nvme &&
        left_admin == right_admin;
}

int cosmos_pcie_residual_oracle_nvme_cmd_word_status(unsigned int word) {
    unsigned int queue_id;
    unsigned int slot_tag;

    if ((word & 0x80000000U) == 0U) {
        return ORACLE_UNAVAILABLE;
    }
    if ((word & 0x7F0080F0U) != 0U) {
        return ORACLE_HW_ERROR;
    }
    queue_id = word & 0xFU;
    slot_tag = (word & 0x7F00U) >> 8U;
    if (queue_id > 8U || slot_tag >= 128U) {
        return ORACLE_HW_ERROR;
    }
    return ORACLE_OK;
}

int cosmos_pcie_residual_oracle_nvme_completion_fields_valid(
    unsigned int queue_id, unsigned int slot_tag,
    unsigned int sequence, unsigned int cid,
    unsigned int status_word) {
    if (queue_id > 8U || slot_tag >= 128U || sequence > 0xFFU ||
        cid > 0xFFFFU || status_word > 0xFFFFU ||
        (status_word & 0x3001U) != 0U) {
        return 0;
    }
    return 1;
}

int cosmos_pcie_residual_oracle_host_dma_device_buffer_status(
    unsigned int device_address, unsigned int length) {
    if ((device_address & 3U) != 0U || length == 0U ||
        length > 0x1000U || (length & 3U) != 0U ||
        device_address < 0x10000000U || device_address > 0x110FFFFFU ||
        length - 1U > 0x110FFFFFU - device_address) {
        return ORACLE_INVALID;
    }
    return ORACLE_OK;
}

int cosmos_pcie_residual_oracle_host_dma_direct_status(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
    unsigned int last_host_address_low;

    if (cosmos_pcie_residual_oracle_host_dma_device_buffer_status(
            device_address, length) != ORACLE_OK ||
        (host_address_low & 15U) != 0U || host_address_high > 15U) {
        return ORACLE_INVALID;
    }
    last_host_address_low = host_address_low + length - 1U;
    if (last_host_address_low < host_address_low && host_address_high == 15U) {
        return ORACLE_INVALID;
    }
    return ORACLE_OK;
}

unsigned int cosmos_pcie_residual_oracle_host_dma_counter_shift(
    unsigned int direct, unsigned int direction) {
    if (direct != 0U) {
        return direction == 0U ? 0U : 8U;
    }
    return direction == 0U ? 16U : 24U;
}

unsigned int cosmos_pcie_residual_oracle_host_dma_counter_index(
    unsigned int direct, unsigned int direction) {
    return cosmos_pcie_residual_oracle_host_dma_counter_shift(
        direct, direction) / 8U;
}

unsigned int cosmos_pcie_residual_oracle_host_dma_direct_word3(
    unsigned int direction, unsigned int length) {
    return (1U << 31U) | (direction << 30U) | length;
}

int cosmos_pcie_residual_oracle_host_dma_auto_status(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address) {
    if (command_slot_tag > 0x7FU || command_4k_offset > 255U ||
        cosmos_pcie_residual_oracle_host_dma_device_buffer_status(
            device_address, 0x1000U) != ORACLE_OK) {
        return ORACLE_INVALID;
    }
    return ORACLE_OK;
}

unsigned int cosmos_pcie_residual_oracle_host_dma_auto_word3(
    unsigned int direction, unsigned int command_slot_tag,
    unsigned int command_4k_offset) {
    return (direction << 30U) | (command_slot_tag << 23U) |
        (command_4k_offset << 14U);
}

unsigned int cosmos_pcie_residual_oracle_nvme_completion_word2(
    unsigned int slot_tag, unsigned int status_word) {
    return ((status_word & 0xFFFFU) << 16U) | (1U << 14U) |
        (slot_tag & 0x7FU);
}
