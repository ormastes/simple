/* Frozen independent C oracle copied from the pre-migration adapter owner. */
#include "cosmos_nvme_pcie_adapter_policy_oracle.h"

#define O_IO_NONE 0U
#define O_IO_RW 1U
#define O_IO_FLUSH 2U
#define O_IO_WRITE_ZEROES 3U
#define O_IO_DSM 4U
#define O_ADMIN_NONE 0U
#define O_ADMIN_QUEUE 1U
#define O_ADMIN_IDENTIFY 2U
#define O_ADMIN_GET_LOG 3U
#define O_PAGE_BYTES 4096U
#define O_PAGE_MASK 4095U

static unsigned long long o_address(unsigned int low, unsigned int high) {
    return ((unsigned long long)high << 32U) | (unsigned long long)low;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_command_cid(unsigned int dw0) {
    return dw0 >> 16U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_command_opcode(unsigned int dw0) {
    return dw0 & 0xFFU;
}

int cosmos_nvme_pcie_adapter_oracle_capacity_valid(
    unsigned int low, unsigned int high) {
    return low != 0U || high != 0U;
}

int cosmos_nvme_pcie_adapter_oracle_block_bytes_valid(unsigned int bytes) {
    return bytes != 0U && (bytes & (bytes - 1U)) == 0U &&
        (bytes & 3U) == 0U;
}

int cosmos_nvme_pcie_adapter_oracle_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5) {
    return (dw0 & 0x0000FF00U) == 0U && dw2 == 0U && dw3 == 0U &&
        dw4 == 0U && dw5 == 0U;
}

int cosmos_nvme_pcie_adapter_oracle_rw_fields_supported(
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15) {
    return (dw12 & ~(0x0000FFFFU | 0xC0000000U)) == 0U &&
        dw13 == 0U && dw14 == 0U && dw15 == 0U;
}

int cosmos_nvme_pcie_adapter_oracle_flush_fields_supported(
    unsigned int dw6, unsigned int dw7, unsigned int dw8,
    unsigned int dw9, unsigned int dw10, unsigned int dw11,
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15) {
    return dw6 == 0U && dw7 == 0U && dw8 == 0U && dw9 == 0U &&
        dw10 == 0U && dw11 == 0U && dw12 == 0U && dw13 == 0U &&
        dw14 == 0U && dw15 == 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_transfer_bytes(
    unsigned int nlb, unsigned int block_bytes) {
    unsigned int count = nlb + 1U;
    if (count == 0U || block_bytes == 0U ||
        count > 0xFFFFFFFFU / block_bytes) {
        return 0U;
    }
    return count * block_bytes;
}

int cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes) {
    unsigned long long prp1 = o_address(low1, high1);
    unsigned long long prp2 = o_address(low2, high2);
    unsigned int first_room;
    unsigned int boundaries;
    if (prp1 == 0ULL || bytes == 0U || bytes > 1048576U || high1 > 15U ||
        high2 > 15U || (low1 & 15U) != 0U) {
        return 0;
    }
    first_room = O_PAGE_BYTES - (unsigned int)(prp1 & O_PAGE_MASK);
    if (bytes <= first_room) {
        return prp2 == 0ULL;
    }
    if (prp2 == 0ULL) {
        return 0;
    }
    boundaries = (bytes - first_room + O_PAGE_BYTES - 1U) / O_PAGE_BYTES;
    if (boundaries == 1U) {
        return (prp2 & O_PAGE_MASK) == 0ULL;
    }
    return (prp2 & 15ULL) == 0ULL;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_prp_first_bytes(
    unsigned int low1, unsigned int bytes) {
    unsigned int room = O_PAGE_BYTES - (low1 & O_PAGE_MASK);
    return room > bytes ? bytes : room;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_io_kind(unsigned int opcode) {
    if (opcode == 0x01U || opcode == 0x02U) return O_IO_RW;
    if (opcode == 0x00U) return O_IO_FLUSH;
    if (opcode == 0x08U) return O_IO_WRITE_ZEROES;
    if (opcode == 0x09U) return O_IO_DSM;
    return O_IO_NONE;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_io_nlb(unsigned int dw12) {
    return dw12 & 0xFFFFU;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_rw_control(unsigned int dw12) {
    return dw12 & 0xC0000000U;
}

int cosmos_nvme_pcie_adapter_oracle_rw_decode_valid(
    unsigned int common, unsigned int fields, unsigned int bytes,
    unsigned int prp) {
    return common != 0U && fields != 0U && bytes != 0U && prp != 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_write_zeroes_control(
    unsigned int dw12) {
    return dw12 & ~0xFFFFU;
}

int cosmos_nvme_pcie_adapter_oracle_write_zeroes_fields_supported(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2) {
    return low1 == 0U && high1 == 0U && low2 == 0U && high2 == 0U;
}

int cosmos_nvme_pcie_adapter_oracle_write_zeroes_decode_valid(
    unsigned int common, unsigned int fields) {
    return common != 0U && fields != 0U;
}

int cosmos_nvme_pcie_adapter_oracle_dsm_fields_supported(
    unsigned int dw10, unsigned int dw12, unsigned int dw13,
    unsigned int dw14, unsigned int dw15) {
    return (dw10 & ~0xFFU) == 0U && dw12 == 0U && dw13 == 0U &&
        dw14 == 0U && dw15 == 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_range_count(
    unsigned int dw10) {
    return (dw10 & 0xFFU) + 1U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_attributes(
    unsigned int dw11) {
    return dw11;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_data_bytes(
    unsigned int ranges) {
    return ranges * 16U;
}

int cosmos_nvme_pcie_adapter_oracle_dsm_decode_valid(
    unsigned int common, unsigned int fields, unsigned int prp) {
    return common != 0U && fields != 0U && prp != 0U;
}

int cosmos_nvme_pcie_adapter_oracle_flush_decode_valid(
    unsigned int common, unsigned int fields) {
    return common != 0U && fields != 0U;
}

int cosmos_nvme_pcie_adapter_oracle_io_invalid_field(
    unsigned int kind, unsigned int valid) {
    return kind != O_IO_NONE && valid == 0U;
}

int cosmos_nvme_pcie_adapter_oracle_admin_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5, unsigned int dw14,
    unsigned int dw15) {
    return (dw0 & 0x0000FF00U) == 0U && dw2 == 0U && dw3 == 0U &&
        dw4 == 0U && dw5 == 0U && dw14 == 0U && dw15 == 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_admin_kind(unsigned int opcode) {
    if (opcode == 0x01U || opcode == 0x05U) return O_ADMIN_QUEUE;
    if (opcode == 0x06U) return O_ADMIN_IDENTIFY;
    if (opcode == 0x02U) return O_ADMIN_GET_LOG;
    return O_ADMIN_NONE;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_admin_payload_bytes(
    unsigned int kind, unsigned int cdw10) {
    if (kind == O_ADMIN_IDENTIFY) return 4096U;
    if (kind == O_ADMIN_GET_LOG) return ((cdw10 >> 16U) + 1U) * 4U;
    return 0U;
}

int cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
    unsigned int kind, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes) {
    if (kind == O_ADMIN_QUEUE) {
        return (low1 != 0U || high1 != 0U) && (low1 & O_PAGE_MASK) == 0U &&
            high1 <= 15U && low2 == 0U && high2 == 0U;
    }
    if (kind == O_ADMIN_IDENTIFY || kind == O_ADMIN_GET_LOG) {
        return cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
            low1, high1, low2, high2, bytes);
    }
    return low1 == 0U && high1 == 0U && low2 == 0U && high2 == 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_admin_invalid_field(
    unsigned int common, unsigned int transfer) {
    return common == 0U || transfer == 0U ? 1U : 0U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_post_result(unsigned int result) {
    if (result == 1U) return 0U;
    if (result == 0U) return 1U;
    if (result == 2U) return 2U;
    return 3U;
}

int cosmos_nvme_pcie_adapter_oracle_admin_payload_request_valid(
    unsigned int low1, unsigned int high1, unsigned int high2,
    unsigned int bytes) {
    return bytes != 0U && bytes <= 4096U && (low1 & 15U) == 0U &&
        high1 <= 15U && high2 <= 15U;
}

unsigned int cosmos_nvme_pcie_adapter_oracle_admin_payload_result(int status) {
    return status == 0 ? 0U : 2U;
}

int cosmos_nvme_pcie_adapter_oracle_no_async_result(void) {
    return 1;
}

int cosmos_nvme_pcie_adapter_oracle_init_values_valid(
    unsigned int low, unsigned int high, unsigned int block_bytes) {
    return cosmos_nvme_pcie_adapter_oracle_capacity_valid(low, high) &&
        cosmos_nvme_pcie_adapter_oracle_block_bytes_valid(block_bytes);
}

int cosmos_nvme_pcie_adapter_oracle_frozen_selfcheck(void) {
    return cosmos_nvme_pcie_adapter_oracle_transfer_bytes(1U, 512U) == 1024U &&
        cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
            0x1FF0U, 0U, 0x3000U, 0U, 32U) == 1 &&
        cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
            0x1FF0U, 0U, 0x3004U, 0U, 32U) == 0 &&
        cosmos_nvme_pcie_adapter_oracle_admin_payload_bytes(
            O_ADMIN_GET_LOG, 0x00030000U) == 16U &&
        cosmos_nvme_pcie_adapter_oracle_post_result(7U) == 3U;
}
