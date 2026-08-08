/*
 * Minimal PCIe-to-service bridge. This only translates the authoritative
 * Cosmos+ PCIe command/completion transport into the bounded NVMe service
 * contract; media and persistence stay with the caller-supplied callbacks.
 */
#include <stdint.h>

#include "cosmos_nvme_pcie_adapter.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_pcie_regs.h"

#define COSMOS_NVME_DW0_OPCODE_MASK       0x000000FFU
#define COSMOS_NVME_DW0_UNSUPPORTED_MASK  0x0000FF00U
#define COSMOS_NVME_DW12_NLB_MASK         0x0000FFFFU
#define COSMOS_NVME_DSM_NR_MASK            0x000000FFU
#define COSMOS_NVME_PRP_PAGE_BYTES        4096U
#define COSMOS_NVME_PRP_PAGE_MASK         (COSMOS_NVME_PRP_PAGE_BYTES - 1U)
#define COSMOS_NVME_PCIE_MAX_TRANSFER_BYTES \
    ((COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX + 1U) * \
     COSMOS_NVME_PRP_PAGE_BYTES)

static unsigned long long cosmos_nvme_u64(unsigned int low,
                                           unsigned int high) {
    return ((unsigned long long)high << 32U) | (unsigned long long)low;
}

static int cosmos_nvme_pcie_capacity_zero(unsigned int low,
                                           unsigned int high) {
    return low == 0U && high == 0U;
}

static int cosmos_nvme_pcie_block_bytes_valid(unsigned int block_bytes) {
    return block_bytes != 0U &&
        (block_bytes & (block_bytes - 1U)) == 0U &&
        (block_bytes & (COSMOS_NVME_DMA_ALIGNMENT - 1U)) == 0U;
}

static void cosmos_nvme_pcie_invalid_field_command(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = raw->raw_dword[0] >> 16U;
    command->namespace_id = COSMOS_NVME_NAMESPACE_ID;
    command->opcode = COSMOS_NVME_OPCODE_FLUSH;
    command->lba_low = 0U;
    command->lba_high = 0U;
    command->nlb = 0U;
    command->data_address_low = 0U;
    command->data_address_high = 0U;
    command->data_address2_low = 0U;
    command->data_address2_high = 0U;
    command->data_bytes = 1U;
    command->control = 0U;
    command->dataset_attributes = 0U;
    command->dataset_range_count = 0U;
}

static int cosmos_nvme_pcie_common_fields_supported(
    const struct cosmos_pcie_nvme_command *raw) {
    return (raw->raw_dword[0] & COSMOS_NVME_DW0_UNSUPPORTED_MASK) == 0U &&
        raw->raw_dword[2] == 0U && raw->raw_dword[3] == 0U &&
        raw->raw_dword[4] == 0U && raw->raw_dword[5] == 0U;
}

static int cosmos_nvme_pcie_rw_fields_supported(
    const struct cosmos_pcie_nvme_command *raw) {
    return (raw->raw_dword[12] &
            ~(COSMOS_NVME_DW12_NLB_MASK |
              COSMOS_NVME_RW_CONTROL_MASK)) == 0U &&
        raw->raw_dword[13] == 0U && raw->raw_dword[14] == 0U &&
        raw->raw_dword[15] == 0U;
}

static int cosmos_nvme_pcie_flush_fields_supported(
    const struct cosmos_pcie_nvme_command *raw) {
    unsigned int index;

    for (index = 6U; index < COSMOS_PCIE_NVME_CMD_DWORDS; ++index) {
        if (raw->raw_dword[index] != 0U) {
            return 0;
        }
    }
    return 1;
}

static int cosmos_nvme_pcie_transfer_bytes(unsigned int nlb,
                                            unsigned int block_bytes,
                                            unsigned int *data_bytes) {
    unsigned int block_count = nlb + 1U;

    if (block_count == 0U || block_bytes == 0U ||
        block_count > (~0U / block_bytes)) {
        return 0;
    }
    *data_bytes = block_count * block_bytes;
    return 1;
}

static int cosmos_nvme_pcie_prp_span_valid(
    unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_low, unsigned int prp2_high,
    unsigned int data_bytes) {
    unsigned long long prp1 = cosmos_nvme_u64(prp1_low, prp1_high);
    unsigned long long prp2 = cosmos_nvme_u64(prp2_low, prp2_high);
    unsigned int boundaries;
    unsigned int first_room;

    if (prp1 == 0ULL || data_bytes == 0U ||
        data_bytes > COSMOS_NVME_PCIE_MAX_TRANSFER_BYTES ||
        prp1_high > 0xFU || prp2_high > 0xFU ||
        (prp1_low & (COSMOS_PCIE_HOST_DMA_HOST_ALIGNMENT - 1U)) != 0U) {
        return 0;
    }

    first_room = COSMOS_NVME_PRP_PAGE_BYTES -
        (unsigned int)(prp1 & COSMOS_NVME_PRP_PAGE_MASK);
    if (data_bytes <= first_room) {
        return prp2 == 0ULL;
    }
    if (prp2 == 0ULL) {
        return 0;
    }
    boundaries =
        (data_bytes - first_room + COSMOS_NVME_PRP_PAGE_BYTES - 1U) /
        COSMOS_NVME_PRP_PAGE_BYTES;
    if (boundaries == 1U) {
        return (prp2 & COSMOS_NVME_PRP_PAGE_MASK) == 0ULL;
    }
    return (prp2 &
            (COSMOS_PCIE_HOST_DMA_HOST_ALIGNMENT - 1U)) == 0ULL;
}

static void cosmos_nvme_pcie_decode_identity(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = raw->raw_dword[0] >> 16U;
    command->namespace_id = raw->raw_dword[1];
    command->opcode = raw->raw_dword[0] & COSMOS_NVME_DW0_OPCODE_MASK;
    command->lba_low = 0U;
    command->lba_high = 0U;
    command->nlb = 0U;
    command->data_address_low = 0U;
    command->data_address_high = 0U;
    command->data_address2_low = 0U;
    command->data_address2_high = 0U;
    command->data_bytes = 0U;
    command->control = 0U;
    command->dataset_attributes = 0U;
    command->dataset_range_count = 0U;
}

static int cosmos_nvme_pcie_decode_rw(
    const struct cosmos_nvme_pcie_bridge *bridge,
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    unsigned int data_bytes;

    command->lba_low = raw->raw_dword[10];
    command->lba_high = raw->raw_dword[11];
    command->nlb = raw->raw_dword[12] & COSMOS_NVME_DW12_NLB_MASK;
    if (!cosmos_nvme_pcie_transfer_bytes(command->nlb, bridge->block_bytes,
                                         &data_bytes) ||
        !cosmos_nvme_pcie_prp_span_valid(
            raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
            raw->raw_dword[9], data_bytes)) {
        return 0;
    }
    command->data_address_low = raw->raw_dword[6];
    command->data_address_high = raw->raw_dword[7];
    command->data_address2_low = raw->raw_dword[8];
    command->data_address2_high = raw->raw_dword[9];
    command->data_bytes = data_bytes;
    command->control =
        raw->raw_dword[12] & COSMOS_NVME_RW_CONTROL_MASK;
    return 1;
}

static int cosmos_nvme_pcie_decode_write_zeroes(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->lba_low = raw->raw_dword[10];
    command->lba_high = raw->raw_dword[11];
    command->nlb = raw->raw_dword[12] & COSMOS_NVME_DW12_NLB_MASK;
    command->control = raw->raw_dword[12] & ~COSMOS_NVME_DW12_NLB_MASK;
    return raw->raw_dword[6] == 0U && raw->raw_dword[7] == 0U &&
        raw->raw_dword[8] == 0U && raw->raw_dword[9] == 0U;
}

static int cosmos_nvme_pcie_decode_dsm(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    unsigned int range_count;
    unsigned int data_bytes;

    if ((raw->raw_dword[10] & ~COSMOS_NVME_DSM_NR_MASK) != 0U ||
        raw->raw_dword[12] != 0U || raw->raw_dword[13] != 0U ||
        raw->raw_dword[14] != 0U || raw->raw_dword[15] != 0U) {
        return 0;
    }
    range_count = (raw->raw_dword[10] & COSMOS_NVME_DSM_NR_MASK) + 1U;
    data_bytes = range_count * COSMOS_NVME_DSM_RANGE_BYTES;
    if (!cosmos_nvme_pcie_prp_span_valid(
            raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
            raw->raw_dword[9], data_bytes)) {
        return 0;
    }
    command->dataset_attributes = raw->raw_dword[11];
    command->dataset_range_count = range_count;
    command->data_address_low = raw->raw_dword[6];
    command->data_address_high = raw->raw_dword[7];
    command->data_address2_low = raw->raw_dword[8];
    command->data_address2_high = raw->raw_dword[9];
    command->data_bytes = data_bytes;
    return 1;
}

int cosmos_nvme_pcie_decode_io(
    const struct cosmos_nvme_pcie_bridge *bridge,
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    unsigned int opcode;

    if (bridge == 0 || raw == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    cosmos_nvme_pcie_decode_identity(raw, command);
    opcode = command->opcode;
    if (opcode == COSMOS_NVME_OPCODE_READ ||
        opcode == COSMOS_NVME_OPCODE_WRITE) {
        if (!cosmos_nvme_pcie_common_fields_supported(raw) ||
            !cosmos_nvme_pcie_rw_fields_supported(raw) ||
            !cosmos_nvme_pcie_decode_rw(bridge, raw, command)) {
            cosmos_nvme_pcie_invalid_field_command(raw, command);
        }
        return COSMOS_OK;
    }
    if (opcode == COSMOS_NVME_OPCODE_FLUSH) {
        if (!cosmos_nvme_pcie_common_fields_supported(raw) ||
            !cosmos_nvme_pcie_flush_fields_supported(raw)) {
            cosmos_nvme_pcie_invalid_field_command(raw, command);
        }
        return COSMOS_OK;
    }
    if (opcode == COSMOS_NVME_OPCODE_WRITE_ZEROES) {
        if (!cosmos_nvme_pcie_common_fields_supported(raw) ||
            !cosmos_nvme_pcie_decode_write_zeroes(raw, command)) {
            cosmos_nvme_pcie_invalid_field_command(raw, command);
        }
        return COSMOS_OK;
    }
    if (opcode == COSMOS_NVME_OPCODE_DATASET_MANAGEMENT) {
        if (!cosmos_nvme_pcie_common_fields_supported(raw) ||
            !cosmos_nvme_pcie_decode_dsm(raw, command)) {
            cosmos_nvme_pcie_invalid_field_command(raw, command);
        }
        return COSMOS_OK;
    }
    return COSMOS_OK;
}

static int cosmos_nvme_pcie_admin_common_fields_supported(
    const struct cosmos_pcie_nvme_command *raw) {
    return (raw->raw_dword[0] & COSMOS_NVME_DW0_UNSUPPORTED_MASK) == 0U &&
        raw->raw_dword[2] == 0U && raw->raw_dword[3] == 0U &&
        raw->raw_dword[4] == 0U && raw->raw_dword[5] == 0U &&
        raw->raw_dword[14] == 0U && raw->raw_dword[15] == 0U;
}

int cosmos_nvme_pcie_decode_admin(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_admin_command *command) {
    unsigned int opcode;
    unsigned int payload_bytes = 0U;

    if (raw == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    opcode = raw->raw_dword[0] & COSMOS_NVME_DW0_OPCODE_MASK;
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = raw->raw_dword[0] >> 16U;
    command->opcode = opcode;
    command->namespace_id = raw->raw_dword[1];
    command->cdw10 = raw->raw_dword[10];
    command->cdw11 = raw->raw_dword[11];
    command->cdw12 = raw->raw_dword[12];
    command->cdw13 = raw->raw_dword[13];
    command->payload_address_low = 0U;
    command->payload_address_high = 0U;
    command->payload_address2_low = 0U;
    command->payload_address2_high = 0U;
    command->payload_bytes = 0U;
    command->invalid_field =
        cosmos_nvme_pcie_admin_common_fields_supported(raw) ? 0U : 1U;

    if (opcode == COSMOS_NVME_ADMIN_CREATE_IO_SQ ||
        opcode == COSMOS_NVME_ADMIN_CREATE_IO_CQ) {
        command->payload_address_low = raw->raw_dword[6];
        command->payload_address_high = raw->raw_dword[7];
        if ((raw->raw_dword[6] == 0U && raw->raw_dword[7] == 0U) ||
            (raw->raw_dword[6] & 0xFFFU) != 0U ||
            raw->raw_dword[7] > 0xFU ||
            raw->raw_dword[8] != 0U || raw->raw_dword[9] != 0U) {
            command->invalid_field = 1U;
        }
        return COSMOS_OK;
    }
    if (opcode == COSMOS_NVME_ADMIN_IDENTIFY) {
        payload_bytes = COSMOS_NVME_ADMIN_IDENTIFY_BYTES;
    } else if (opcode == COSMOS_NVME_ADMIN_GET_LOG_PAGE) {
        payload_bytes = ((raw->raw_dword[10] >> 16U) + 1U) * 4U;
    }
    if (payload_bytes != 0U) {
        if (!cosmos_nvme_pcie_prp_span_valid(
                raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
                raw->raw_dword[9], payload_bytes)) {
            command->invalid_field = 1U;
            return COSMOS_OK;
        }
        command->payload_address_low = raw->raw_dword[6];
        command->payload_address_high = raw->raw_dword[7];
        command->payload_address2_low = raw->raw_dword[8];
        command->payload_address2_high = raw->raw_dword[9];
        command->payload_bytes = payload_bytes;
    } else if (raw->raw_dword[6] != 0U || raw->raw_dword[7] != 0U ||
               raw->raw_dword[8] != 0U || raw->raw_dword[9] != 0U) {
        command->invalid_field = 1U;
    }
    return COSMOS_OK;
}

static enum cosmos_nvme_post_result cosmos_nvme_pcie_post_result(
    enum cosmos_pcie_nvme_completion_result result) {
    if (result == COSMOS_PCIE_NVME_COMPLETION_COMMITTED) {
        return COSMOS_NVME_POST_COMMITTED;
    }
    if (result == COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED) {
        return COSMOS_NVME_POST_NOT_COMMITTED_RETRY;
    }
    if (result == COSMOS_PCIE_NVME_COMPLETION_AMBIGUOUS) {
        return COSMOS_NVME_POST_AMBIGUOUS;
    }
    return COSMOS_NVME_POST_HARD_FAILED;
}

static enum cosmos_nvme_post_result cosmos_nvme_pcie_post_completion(
    void *context, const struct cosmos_nvme_completion *completion) {
    enum cosmos_pcie_nvme_completion_result result;

    if (context == 0 || completion == 0) {
        return COSMOS_NVME_POST_HARD_FAILED;
    }
    result = cosmos_pcie_nvme_post_completion_fields(
        completion->queue_id, completion->slot_tag, completion->sequence,
        completion->cid, 0U, completion->status.sct, completion->status.sc,
        completion->status.dnr);
    return cosmos_nvme_pcie_post_result(result);
}

enum cosmos_nvme_post_result cosmos_nvme_pcie_post_admin_completion(
    void *context, const struct cosmos_nvme_admin_completion *completion) {
    enum cosmos_pcie_nvme_completion_result result;

    if (context == 0 || completion == 0) {
        return COSMOS_NVME_POST_HARD_FAILED;
    }
    result = cosmos_pcie_nvme_post_completion_fields(
        completion->queue_id, completion->slot_tag, completion->sequence,
        completion->cid, completion->result_low, completion->status.sct,
        completion->status.sc, completion->status.dnr);
    return cosmos_nvme_pcie_post_result(result);
}

int cosmos_nvme_pcie_configure_io_sq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    if (context == 0) {
        return COSMOS_INVALID;
    }
    return cosmos_pcie_nvme_configure_io_sq(
        queue_id, valid, completion_queue_id, entries,
        address_low, address_high);
}

int cosmos_nvme_pcie_configure_io_cq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    if (context == 0) {
        return COSMOS_INVALID;
    }
    return cosmos_pcie_nvme_configure_io_cq(
        queue_id, valid, irq_enable, irq_vector, entries,
        address_low, address_high);
}

static enum cosmos_nvme_admin_payload_result
cosmos_nvme_pcie_write_admin_payload(
    void *context, const struct cosmos_nvme_admin_command *command,
    const unsigned char *payload, unsigned int payload_bytes) {
    volatile unsigned char *staging =
        (volatile unsigned char *)(uintptr_t)COSMOS_NFC_DATA_POOL_BASE;
    unsigned int index;
    unsigned int first_bytes;
    int status;

    if (context == 0 || command == 0 || payload == 0 ||
        payload_bytes == 0U ||
        payload_bytes > COSMOS_PCIE_HOST_DMA_MAX_BYTES ||
        (command->payload_address_low &
         (COSMOS_PCIE_HOST_DMA_HOST_ALIGNMENT - 1U)) != 0U ||
        command->payload_address_high > 0xFU ||
        command->payload_address2_high > 0xFU) {
        return COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED;
    }
    for (index = 0U; index < payload_bytes; ++index) {
        staging[index] = payload[index];
    }
    cosmos_data_sync_barrier();
    first_bytes = COSMOS_NVME_PRP_PAGE_BYTES -
        (command->payload_address_low & COSMOS_NVME_PRP_PAGE_MASK);
    if (first_bytes > payload_bytes) {
        first_bytes = payload_bytes;
    }
    status = cosmos_pcie_host_dma_submit_device_to_host(
        COSMOS_NFC_DATA_POOL_BASE, command->payload_address_high,
        command->payload_address_low, first_bytes);
    if (status == COSMOS_OK) {
        status = cosmos_pcie_host_dma_poll_direct(
            COSMOS_PCIE_DEVICE_TO_HOST);
    }
    if (status == COSMOS_OK && first_bytes < payload_bytes) {
        status = cosmos_pcie_host_dma_submit_device_to_host(
            COSMOS_NFC_DATA_POOL_BASE + first_bytes,
            command->payload_address2_high,
            command->payload_address2_low,
            payload_bytes - first_bytes);
        if (status == COSMOS_OK) {
            status = cosmos_pcie_host_dma_poll_direct(
                COSMOS_PCIE_DEVICE_TO_HOST);
        }
    }
    return status == COSMOS_OK
        ? COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED
        : COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED;
}

static int cosmos_nvme_pcie_no_async_event(
    void *context, unsigned int *result_low) {
    (void)context;
    (void)result_low;
    return COSMOS_UNAVAILABLE;
}

static int cosmos_nvme_pcie_media_read(
    void *context, const struct cosmos_nvme_command *command) {
    struct cosmos_nvme_pcie_bridge *bridge = context;

    if (bridge == 0 || bridge->media_read == 0) {
        return COSMOS_INVALID;
    }
    return bridge->media_read(bridge->media_context, command);
}

static int cosmos_nvme_pcie_media_program(
    void *context, const struct cosmos_nvme_command *command) {
    struct cosmos_nvme_pcie_bridge *bridge = context;

    if (bridge == 0 || bridge->media_program == 0) {
        return COSMOS_INVALID;
    }
    return bridge->media_program(bridge->media_context, command);
}

static int cosmos_nvme_pcie_media_flush(void *context) {
    struct cosmos_nvme_pcie_bridge *bridge = context;

    if (bridge == 0 || bridge->media_flush == 0) {
        return COSMOS_INVALID;
    }
    return bridge->media_flush(bridge->media_context);
}

static int cosmos_nvme_pcie_media_write_zeroes(
    void *context, const struct cosmos_nvme_command *command) {
    struct cosmos_nvme_pcie_bridge *bridge = context;

    if (bridge == 0 || bridge->media_write_zeroes == 0) {
        return COSMOS_INVALID;
    }
    return bridge->media_write_zeroes(bridge->media_context, command);
}

static int cosmos_nvme_pcie_media_deallocate(
    void *context, const struct cosmos_nvme_command *command) {
    struct cosmos_nvme_pcie_bridge *bridge = context;

    if (bridge == 0 || bridge->media_deallocate == 0) {
        return COSMOS_INVALID;
    }
    return bridge->media_deallocate(bridge->media_context, command);
}

int cosmos_nvme_pcie_service_init(
    struct cosmos_nvme_service *service,
    struct cosmos_nvme_pcie_bridge *bridge,
    void *media_context,
    cosmos_nvme_pcie_media_io_fn media_read,
    cosmos_nvme_pcie_media_io_fn media_program,
    cosmos_nvme_pcie_media_flush_fn media_flush,
    cosmos_nvme_pcie_media_zeroes_fn media_write_zeroes,
    cosmos_nvme_pcie_media_deallocate_fn media_deallocate,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high,
    unsigned int block_bytes) {
    struct cosmos_nvme_adapter adapter;

    if (service == 0 || bridge == 0 || media_context == 0 ||
        media_read == 0 || media_program == 0 || media_flush == 0 ||
        media_write_zeroes == 0 || media_deallocate == 0 ||
        cosmos_nvme_pcie_capacity_zero(namespace_blocks_low,
                                       namespace_blocks_high) ||
        !cosmos_nvme_pcie_block_bytes_valid(block_bytes)) {
        return COSMOS_INVALID;
    }

    bridge->media_context = media_context;
    bridge->media_read = media_read;
    bridge->media_program = media_program;
    bridge->media_flush = media_flush;
    bridge->media_write_zeroes = media_write_zeroes;
    bridge->media_deallocate = media_deallocate;
    bridge->block_bytes = block_bytes;

    adapter.context = bridge;
    adapter.fetch_command = 0;
    adapter.post_completion = cosmos_nvme_pcie_post_completion;
    adapter.media_read = cosmos_nvme_pcie_media_read;
    adapter.media_program = cosmos_nvme_pcie_media_program;
    adapter.media_flush = cosmos_nvme_pcie_media_flush;
    adapter.media_write_zeroes = cosmos_nvme_pcie_media_write_zeroes;
    adapter.media_deallocate = cosmos_nvme_pcie_media_deallocate;
    return cosmos_nvme_service_init(service, &adapter, namespace_blocks_low,
                                    namespace_blocks_high, block_bytes);
}

int cosmos_nvme_pcie_admin_service_init(
    struct cosmos_nvme_admin_service *service,
    struct cosmos_nvme_pcie_bridge *bridge,
    unsigned int namespace_blocks_low,
    unsigned int namespace_blocks_high,
    unsigned int block_bytes) {
    struct cosmos_nvme_admin_adapter adapter;

    if (service == 0 || bridge == 0) {
        return COSMOS_INVALID;
    }
    adapter.context = bridge;
    adapter.fetch_command = 0;
    adapter.post_completion = cosmos_nvme_pcie_post_admin_completion;
    adapter.write_payload = cosmos_nvme_pcie_write_admin_payload;
    adapter.poll_async_event = cosmos_nvme_pcie_no_async_event;
    adapter.configure_io_sq = cosmos_nvme_pcie_configure_io_sq;
    adapter.configure_io_cq = cosmos_nvme_pcie_configure_io_cq;
    return cosmos_nvme_admin_init(
        service, &adapter, namespace_blocks_low,
        namespace_blocks_high, block_bytes);
}
