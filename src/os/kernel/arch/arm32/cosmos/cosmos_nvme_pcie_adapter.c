/*
 * Minimal PCIe-to-service bridge. This only translates the authoritative
 * Cosmos+ PCIe command/completion transport into the bounded NVMe service
 * contract; media and persistence stay with the caller-supplied callbacks.
 */
#include <stdint.h>

#include "cosmos_nvme_pcie_adapter.h"
#include "cosmos_nvme_pcie_adapter_policy.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_pcie_regs.h"

static void cosmos_nvme_pcie_invalid_field_command(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = cosmos_nvme_pcie_adapter_policy_command_cid(
        raw->raw_dword[0]);
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

static void cosmos_nvme_pcie_decode_identity(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = cosmos_nvme_pcie_adapter_policy_command_cid(
        raw->raw_dword[0]);
    command->namespace_id = raw->raw_dword[1];
    command->opcode = cosmos_nvme_pcie_adapter_policy_command_opcode(
        raw->raw_dword[0]);
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
    command->nlb = cosmos_nvme_pcie_adapter_policy_io_nlb(
        raw->raw_dword[12]);
    data_bytes = cosmos_nvme_pcie_adapter_policy_transfer_bytes(
        command->nlb, bridge->block_bytes);
    command->data_address_low = raw->raw_dword[6];
    command->data_address_high = raw->raw_dword[7];
    command->data_address2_low = raw->raw_dword[8];
    command->data_address2_high = raw->raw_dword[9];
    command->data_bytes = data_bytes;
    command->control = cosmos_nvme_pcie_adapter_policy_rw_control(
        raw->raw_dword[12]);
    return cosmos_nvme_pcie_adapter_policy_rw_decode_valid(
        (unsigned int)cosmos_nvme_pcie_adapter_policy_common_fields_supported(
            raw->raw_dword[0], raw->raw_dword[2], raw->raw_dword[3],
            raw->raw_dword[4], raw->raw_dword[5]),
        (unsigned int)cosmos_nvme_pcie_adapter_policy_rw_fields_supported(
            raw->raw_dword[12], raw->raw_dword[13], raw->raw_dword[14],
            raw->raw_dword[15]),
        data_bytes,
        (unsigned int)cosmos_nvme_pcie_adapter_policy_prp_span_valid(
            raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
            raw->raw_dword[9], data_bytes));
}

static int cosmos_nvme_pcie_decode_write_zeroes(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    command->lba_low = raw->raw_dword[10];
    command->lba_high = raw->raw_dword[11];
    command->nlb = cosmos_nvme_pcie_adapter_policy_io_nlb(
        raw->raw_dword[12]);
    command->control =
        cosmos_nvme_pcie_adapter_policy_write_zeroes_control(
            raw->raw_dword[12]);
    return cosmos_nvme_pcie_adapter_policy_write_zeroes_decode_valid(
        (unsigned int)cosmos_nvme_pcie_adapter_policy_common_fields_supported(
            raw->raw_dword[0], raw->raw_dword[2], raw->raw_dword[3],
            raw->raw_dword[4], raw->raw_dword[5]),
        (unsigned int)
            cosmos_nvme_pcie_adapter_policy_write_zeroes_fields_supported(
                raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
                raw->raw_dword[9]));
}

static int cosmos_nvme_pcie_decode_dsm(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    unsigned int range_count;
    unsigned int data_bytes;

    range_count = cosmos_nvme_pcie_adapter_policy_dsm_range_count(
        raw->raw_dword[10]);
    data_bytes = cosmos_nvme_pcie_adapter_policy_dsm_data_bytes(range_count);
    command->dataset_attributes =
        cosmos_nvme_pcie_adapter_policy_dsm_attributes(raw->raw_dword[11]);
    command->dataset_range_count = range_count;
    command->data_address_low = raw->raw_dword[6];
    command->data_address_high = raw->raw_dword[7];
    command->data_address2_low = raw->raw_dword[8];
    command->data_address2_high = raw->raw_dword[9];
    command->data_bytes = data_bytes;
    return cosmos_nvme_pcie_adapter_policy_dsm_decode_valid(
        (unsigned int)cosmos_nvme_pcie_adapter_policy_common_fields_supported(
            raw->raw_dword[0], raw->raw_dword[2], raw->raw_dword[3],
            raw->raw_dword[4], raw->raw_dword[5]),
        (unsigned int)cosmos_nvme_pcie_adapter_policy_dsm_fields_supported(
            raw->raw_dword[10], raw->raw_dword[12], raw->raw_dword[13],
            raw->raw_dword[14], raw->raw_dword[15]),
        (unsigned int)cosmos_nvme_pcie_adapter_policy_prp_span_valid(
            raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
            raw->raw_dword[9], data_bytes));
}

int cosmos_nvme_pcie_decode_io(
    const struct cosmos_nvme_pcie_bridge *bridge,
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_command *command) {
    unsigned int kind;
    unsigned int specific_valid = 1U;

    if (bridge == 0 || raw == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    cosmos_nvme_pcie_decode_identity(raw, command);
    kind = cosmos_nvme_pcie_adapter_policy_io_kind(command->opcode);
    if (kind == COSMOS_NVME_PCIE_ADAPTER_IO_RW) {
        specific_valid = (unsigned int)cosmos_nvme_pcie_decode_rw(
            bridge, raw, command);
    } else if (kind == COSMOS_NVME_PCIE_ADAPTER_IO_FLUSH) {
        specific_valid = (unsigned int)
            cosmos_nvme_pcie_adapter_policy_flush_decode_valid(
                (unsigned int)
                    cosmos_nvme_pcie_adapter_policy_common_fields_supported(
                        raw->raw_dword[0], raw->raw_dword[2],
                        raw->raw_dword[3], raw->raw_dword[4],
                        raw->raw_dword[5]),
                (unsigned int)
                    cosmos_nvme_pcie_adapter_policy_flush_fields_supported(
                        raw->raw_dword[6], raw->raw_dword[7],
                        raw->raw_dword[8], raw->raw_dword[9],
                        raw->raw_dword[10], raw->raw_dword[11],
                        raw->raw_dword[12], raw->raw_dword[13],
                        raw->raw_dword[14], raw->raw_dword[15]));
    } else if (kind == COSMOS_NVME_PCIE_ADAPTER_IO_WRITE_ZEROES) {
        specific_valid = (unsigned int)cosmos_nvme_pcie_decode_write_zeroes(
            raw, command);
    } else if (kind == COSMOS_NVME_PCIE_ADAPTER_IO_DSM) {
        specific_valid = (unsigned int)cosmos_nvme_pcie_decode_dsm(
            raw, command);
    }
    if (cosmos_nvme_pcie_adapter_policy_io_invalid_field(
            kind, specific_valid)) {
        cosmos_nvme_pcie_invalid_field_command(raw, command);
    }
    return COSMOS_OK;
}

int cosmos_nvme_pcie_decode_admin(
    const struct cosmos_pcie_nvme_command *raw,
    struct cosmos_nvme_admin_command *command) {
    unsigned int opcode;
    unsigned int kind;
    unsigned int common_supported;
    unsigned int transfer_valid;
    unsigned int payload_bytes = 0U;

    if (raw == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    opcode = cosmos_nvme_pcie_adapter_policy_command_opcode(
        raw->raw_dword[0]);
    command->queue_id = raw->queue_id;
    command->slot_tag = raw->slot_tag;
    command->sequence = raw->sequence;
    command->cid = cosmos_nvme_pcie_adapter_policy_command_cid(
        raw->raw_dword[0]);
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
    common_supported = (unsigned int)
        cosmos_nvme_pcie_adapter_policy_admin_common_fields_supported(
            raw->raw_dword[0], raw->raw_dword[2], raw->raw_dword[3],
            raw->raw_dword[4], raw->raw_dword[5], raw->raw_dword[14],
            raw->raw_dword[15]);
    kind = cosmos_nvme_pcie_adapter_policy_admin_kind(opcode);
    payload_bytes = cosmos_nvme_pcie_adapter_policy_admin_payload_bytes(
        kind, raw->raw_dword[10]);
    transfer_valid = (unsigned int)
        cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
            kind, raw->raw_dword[6], raw->raw_dword[7], raw->raw_dword[8],
            raw->raw_dword[9], payload_bytes);
    command->invalid_field =
        cosmos_nvme_pcie_adapter_policy_admin_invalid_field(
            common_supported, transfer_valid);

    if (kind == COSMOS_NVME_PCIE_ADAPTER_ADMIN_QUEUE) {
        command->payload_address_low = raw->raw_dword[6];
        command->payload_address_high = raw->raw_dword[7];
        return COSMOS_OK;
    }
    if (payload_bytes != 0U && transfer_valid != 0U) {
        command->payload_address_low = raw->raw_dword[6];
        command->payload_address_high = raw->raw_dword[7];
        command->payload_address2_low = raw->raw_dword[8];
        command->payload_address2_high = raw->raw_dword[9];
        command->payload_bytes = payload_bytes;
    }
    return COSMOS_OK;
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
    return (enum cosmos_nvme_post_result)
        cosmos_nvme_pcie_adapter_policy_post_result((unsigned int)result);
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
    return (enum cosmos_nvme_post_result)
        cosmos_nvme_pcie_adapter_policy_post_result((unsigned int)result);
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
        !cosmos_nvme_pcie_adapter_policy_admin_payload_request_valid(
            command->payload_address_low, command->payload_address_high,
            command->payload_address2_high, payload_bytes)) {
        return COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED;
    }
    for (index = 0U; index < payload_bytes; ++index) {
        staging[index] = payload[index];
    }
    cosmos_data_sync_barrier();
    first_bytes = cosmos_nvme_pcie_adapter_policy_prp_first_bytes(
        command->payload_address_low, payload_bytes);
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
    return (enum cosmos_nvme_admin_payload_result)
        cosmos_nvme_pcie_adapter_policy_admin_payload_result(status);
}

static int cosmos_nvme_pcie_no_async_event(
    void *context, unsigned int *result_low) {
    (void)context;
    (void)result_low;
    return cosmos_nvme_pcie_adapter_policy_no_async_result();
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
        !cosmos_nvme_pcie_adapter_policy_init_values_valid(
            namespace_blocks_low, namespace_blocks_high, block_bytes)) {
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
