/* Bounded one-namespace NVMe command service for the Cosmos+ firmware. */
#include "cosmos_hal.h"

_Static_assert((COSMOS_NVME_DMA_ALIGNMENT &
                (COSMOS_NVME_DMA_ALIGNMENT - 1U)) == 0U,
               "NVMe DMA alignment must be a power of two");

static struct cosmos_nvme_status cosmos_nvme_status_make(unsigned int sct,
                                                           unsigned int sc,
                                                           unsigned int dnr) {
    struct cosmos_nvme_status status;

    status.sct = sct;
    status.sc = sc;
    status.dnr = dnr;
    return status;
}

static struct cosmos_nvme_status cosmos_nvme_status_success(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_SUCCESS, 0U);
}

static struct cosmos_nvme_status cosmos_nvme_status_invalid_opcode(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_INVALID_OPCODE, 1U);
}

static struct cosmos_nvme_status cosmos_nvme_status_invalid_field(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_INVALID_FIELD, 1U);
}

static struct cosmos_nvme_status cosmos_nvme_status_invalid_namespace(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT,
                                   1U);
}

static struct cosmos_nvme_status cosmos_nvme_status_lba_range(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_LBA_OUT_OF_RANGE, 1U);
}

static struct cosmos_nvme_status cosmos_nvme_status_data_transfer(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U);
}

static struct cosmos_nvme_status cosmos_nvme_status_internal(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR, 0U);
}

static struct cosmos_nvme_status cosmos_nvme_status_namespace_not_ready(void) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_GENERIC,
                                   COSMOS_NVME_SC_NAMESPACE_NOT_READY, 0U);
}

static struct cosmos_nvme_status cosmos_nvme_status_media(unsigned int sc) {
    return cosmos_nvme_status_make(COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                                   sc, 0U);
}

static int cosmos_nvme_capacity_is_zero(unsigned int low, unsigned int high) {
    return low == 0U && high == 0U;
}

static int cosmos_nvme_end_within_namespace(
    const struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command,
    unsigned int block_count) {
    unsigned int end_low = command->lba_low + block_count;
    unsigned int carry = end_low < command->lba_low;
    unsigned int end_high = command->lba_high + carry;

    if (end_high < command->lba_high) {
        return 0;
    }
    if (end_high != service->namespace_blocks_high) {
        return end_high < service->namespace_blocks_high;
    }
    return end_low <= service->namespace_blocks_low;
}

static int cosmos_nvme_data_span_valid(
    const struct cosmos_nvme_command *command, unsigned int required) {
    if (command->data_address_low == 0U &&
        command->data_address_high == 0U) {
        return 0;
    }
    if ((command->data_address_low & (COSMOS_NVME_DMA_ALIGNMENT - 1U)) !=
            0U ||
        ((command->data_address2_low != 0U ||
          command->data_address2_high != 0U) &&
         (command->data_address2_low &
          (COSMOS_NVME_DMA_ALIGNMENT - 1U)) != 0U) ||
        command->data_bytes != required) {
        return 0;
    }
    return 1;
}

static int cosmos_nvme_data_transfer_valid(
    const struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command,
    unsigned int block_count) {
    if (block_count > (~0U / service->block_bytes)) {
        return 0;
    }
    return cosmos_nvme_data_span_valid(
        command, block_count * service->block_bytes);
}

static struct cosmos_nvme_status cosmos_nvme_io_validate(
    const struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command, unsigned int *block_count) {
    if (command->cid > COSMOS_NVME_MAX_CID ||
        command->nlb > COSMOS_NVME_MAX_NLB ||
        (command->control & ~COSMOS_NVME_RW_CONTROL_MASK) != 0U) {
        return cosmos_nvme_status_invalid_field();
    }
    if (command->namespace_id != COSMOS_NVME_NAMESPACE_ID) {
        return cosmos_nvme_status_invalid_namespace();
    }
    *block_count = command->nlb + 1U;
    if (!cosmos_nvme_end_within_namespace(service, command, *block_count)) {
        return cosmos_nvme_status_lba_range();
    }
    if (!cosmos_nvme_data_transfer_valid(service, command, *block_count)) {
        return cosmos_nvme_status_data_transfer();
    }
    return cosmos_nvme_status_success();
}

static int cosmos_nvme_status_is_success(struct cosmos_nvme_status status) {
    return status.sct == COSMOS_NVME_SCT_GENERIC &&
        status.sc == COSMOS_NVME_SC_SUCCESS && status.dnr == 0U;
}

static struct cosmos_nvme_status cosmos_nvme_media_status(
    int result, unsigned int media_sc) {
    if (result == COSMOS_OK) {
        return cosmos_nvme_status_success();
    }
    if (result == COSMOS_UNAVAILABLE) {
        return cosmos_nvme_status_namespace_not_ready();
    }
    if (result == COSMOS_TIMEOUT || result == COSMOS_HW_ERROR) {
        return cosmos_nvme_status_media(media_sc);
    }
    return cosmos_nvme_status_internal();
}

static int cosmos_nvme_flush_valid(const struct cosmos_nvme_command *command) {
    return command->cid <= COSMOS_NVME_MAX_CID &&
        command->namespace_id == COSMOS_NVME_NAMESPACE_ID &&
        command->lba_low == 0U && command->lba_high == 0U &&
        command->nlb == 0U && command->data_address_low == 0U &&
        command->data_address_high == 0U &&
        command->data_address2_low == 0U &&
        command->data_address2_high == 0U && command->data_bytes == 0U;
}

static struct cosmos_nvme_status cosmos_nvme_execute(
    struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command) {
    unsigned int block_count;
    struct cosmos_nvme_status status;
    int result;

    if (command->opcode == COSMOS_NVME_OPCODE_FLUSH) {
        if (command->namespace_id != COSMOS_NVME_NAMESPACE_ID) {
            return cosmos_nvme_status_invalid_namespace();
        }
        if (!cosmos_nvme_flush_valid(command)) {
            return cosmos_nvme_status_invalid_field();
        }
        return cosmos_nvme_media_status(
            service->adapter.media_flush(service->adapter.context),
            COSMOS_NVME_SC_WRITE_FAULT);
    }
    if (command->opcode == COSMOS_NVME_OPCODE_WRITE_ZEROES) {
        if (command->namespace_id != COSMOS_NVME_NAMESPACE_ID) {
            return cosmos_nvme_status_invalid_namespace();
        }
        if (command->cid > COSMOS_NVME_MAX_CID ||
            command->nlb > COSMOS_NVME_MAX_NLB ||
            (command->control & ~COSMOS_NVME_WRITE_ZEROES_CONTROL_MASK) != 0U ||
            command->dataset_attributes != 0U ||
            command->dataset_range_count != 0U ||
            command->data_address_low != 0U ||
            command->data_address_high != 0U ||
            command->data_address2_low != 0U ||
            command->data_address2_high != 0U ||
            command->data_bytes != 0U) {
            return cosmos_nvme_status_invalid_field();
        }
        block_count = command->nlb + 1U;
        if (!cosmos_nvme_end_within_namespace(
                service, command, block_count)) {
            return cosmos_nvme_status_lba_range();
        }
        if (service->adapter.media_write_zeroes == 0) {
            return cosmos_nvme_status_invalid_opcode();
        }
        result = service->adapter.media_write_zeroes(
            service->adapter.context, command);
        if (result == COSMOS_OK &&
            (command->control & COSMOS_NVME_WRITE_ZEROES_FUA) != 0U) {
            result = service->adapter.media_flush(service->adapter.context);
        }
        return cosmos_nvme_media_status(result, COSMOS_NVME_SC_WRITE_FAULT);
    }
    if (command->opcode == COSMOS_NVME_OPCODE_DATASET_MANAGEMENT) {
        unsigned int required;

        if (command->namespace_id != COSMOS_NVME_NAMESPACE_ID) {
            return cosmos_nvme_status_invalid_namespace();
        }
        if (command->cid > COSMOS_NVME_MAX_CID ||
            command->dataset_range_count == 0U ||
            command->dataset_range_count > COSMOS_NVME_MAX_DSM_RANGES ||
            (command->dataset_attributes &
             ~COSMOS_NVME_DSM_ATTRIBUTE_MASK) != 0U ||
            command->lba_low != 0U || command->lba_high != 0U ||
            command->nlb != 0U || command->control != 0U ||
            command->dataset_range_count > (~0U / COSMOS_NVME_DSM_RANGE_BYTES)) {
            return cosmos_nvme_status_invalid_field();
        }
        required = command->dataset_range_count * COSMOS_NVME_DSM_RANGE_BYTES;
        if (!cosmos_nvme_data_span_valid(command, required)) {
            return cosmos_nvme_status_data_transfer();
        }
        if ((command->dataset_attributes &
             COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE) == 0U) {
            return cosmos_nvme_status_success();
        }
        if (service->adapter.media_deallocate == 0) {
            return cosmos_nvme_status_invalid_opcode();
        }
        result = service->adapter.media_deallocate(
            service->adapter.context, command);
        return cosmos_nvme_media_status(result, COSMOS_NVME_SC_WRITE_FAULT);
    }
    if (command->opcode != COSMOS_NVME_OPCODE_READ &&
        command->opcode != COSMOS_NVME_OPCODE_WRITE) {
        return cosmos_nvme_status_invalid_opcode();
    }
    status = cosmos_nvme_io_validate(service, command, &block_count);
    if (!cosmos_nvme_status_is_success(status)) {
        return status;
    }
    if (command->opcode == COSMOS_NVME_OPCODE_READ) {
        result = service->adapter.media_read(
            service->adapter.context, command);
    } else {
        result = service->adapter.media_program(
            service->adapter.context, command);
        if (result == COSMOS_OK &&
            (command->control & COSMOS_NVME_RW_FUA) != 0U) {
            result = service->adapter.media_flush(service->adapter.context);
        }
    }
    return cosmos_nvme_media_status(
        result, command->opcode == COSMOS_NVME_OPCODE_READ
            ? COSMOS_NVME_SC_UNRECOVERED_READ_ERROR
            : COSMOS_NVME_SC_WRITE_FAULT);
}

static void cosmos_nvme_completion_from_command(
    struct cosmos_nvme_completion *completion,
    const struct cosmos_nvme_command *command,
    struct cosmos_nvme_status status) {
    completion->queue_id = command->queue_id;
    completion->slot_tag = command->slot_tag;
    completion->sequence = command->sequence;
    completion->cid = command->cid;
    completion->status = status;
}

static int cosmos_nvme_publish_pending(struct cosmos_nvme_service *service) {
    enum cosmos_nvme_post_result result = service->adapter.post_completion(
        service->adapter.context, &service->pending_completion);

    switch (result) {
    case COSMOS_NVME_POST_COMMITTED:
        service->completion_state = COSMOS_NVME_COMPLETION_NONE;
        service->completion_terminal_status = COSMOS_OK;
        return COSMOS_OK;
    case COSMOS_NVME_POST_NOT_COMMITTED_RETRY:
        service->completion_state = COSMOS_NVME_COMPLETION_RETRY;
        return COSMOS_RETRY;
    case COSMOS_NVME_POST_AMBIGUOUS:
        service->completion_state = COSMOS_NVME_COMPLETION_BLOCKED;
        service->completion_terminal_status = COSMOS_COMPLETION_UNCERTAIN;
        return COSMOS_COMPLETION_UNCERTAIN;
    case COSMOS_NVME_POST_HARD_FAILED:
    default:
        service->completion_state = COSMOS_NVME_COMPLETION_BLOCKED;
        service->completion_terminal_status = COSMOS_HW_ERROR;
        return COSMOS_HW_ERROR;
    }
}

int cosmos_nvme_service_init(struct cosmos_nvme_service *service,
                             const struct cosmos_nvme_adapter *adapter,
                             unsigned int namespace_blocks_low,
                             unsigned int namespace_blocks_high,
                             unsigned int block_bytes) {
    if (service == 0 || adapter == 0 || adapter->post_completion == 0 ||
        adapter->media_read == 0 ||
        adapter->media_program == 0 || adapter->media_flush == 0 ||
        cosmos_nvme_capacity_is_zero(namespace_blocks_low,
                                     namespace_blocks_high) ||
        block_bytes == 0U ||
        (block_bytes & (COSMOS_NVME_DMA_ALIGNMENT - 1U)) != 0U) {
        return COSMOS_INVALID;
    }
    service->adapter = *adapter;
    service->namespace_blocks_low = namespace_blocks_low;
    service->namespace_blocks_high = namespace_blocks_high;
    service->block_bytes = block_bytes;
    service->completion_state = COSMOS_NVME_COMPLETION_NONE;
    service->completion_terminal_status = COSMOS_OK;
    service->pending_completion.queue_id = 0U;
    service->pending_completion.slot_tag = 0U;
    service->pending_completion.sequence = 0U;
    service->pending_completion.cid = 0U;
    service->pending_completion.status = cosmos_nvme_status_success();
    return COSMOS_OK;
}

int cosmos_nvme_service_accept(struct cosmos_nvme_service *service,
                               const struct cosmos_nvme_command *command) {
    int status;

    if (service == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_BLOCKED) {
        return service->completion_terminal_status;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_RETRY) {
        status = cosmos_nvme_publish_pending(service);
        if (status != COSMOS_OK) {
            return status;
        }
    }
    cosmos_nvme_completion_from_command(&service->pending_completion, command,
                                        cosmos_nvme_execute(service, command));
    service->completion_state = COSMOS_NVME_COMPLETION_RETRY;
    return cosmos_nvme_publish_pending(service);
}

int cosmos_nvme_service_poll(struct cosmos_nvme_service *service) {
    unsigned int processed;

    if (service == 0) {
        return COSMOS_INVALID;
    }
    for (processed = 0U; processed < COSMOS_NVME_SERVICE_BUDGET;
         processed++) {
        struct cosmos_nvme_command command;
        int status;

        if (service->completion_state == COSMOS_NVME_COMPLETION_BLOCKED) {
            return service->completion_terminal_status;
        }
        if (service->completion_state == COSMOS_NVME_COMPLETION_RETRY) {
            status = cosmos_nvme_publish_pending(service);
            if (status != COSMOS_OK) {
                return status;
            }
        }
        if (service->adapter.fetch_command == 0) {
            return COSMOS_OK;
        }
        status = service->adapter.fetch_command(service->adapter.context,
                                                &command);
        if (status == COSMOS_UNAVAILABLE) {
            return COSMOS_OK;
        }
        if (status != COSMOS_OK) {
            return status;
        }
        status = cosmos_nvme_service_accept(service, &command);
        if (status != COSMOS_OK) {
            return status;
        }
    }
    return COSMOS_OK;
}
