/* Bounded one-namespace NVMe command service for the Cosmos+ firmware. */
#include "cosmos_hal.h"
#include "cosmos_nvme_media_policy.h"

_Static_assert((COSMOS_NVME_DMA_ALIGNMENT &
                (COSMOS_NVME_DMA_ALIGNMENT - 1U)) == 0U,
               "NVMe DMA alignment must be a power of two");

static struct cosmos_nvme_status cosmos_nvme_status_from_policy(
    unsigned int encoded) {
    struct cosmos_nvme_status status;

    status.sct = (encoded >> 8U) & 0xFFU;
    status.sc = encoded & 0xFFU;
    status.dnr = (encoded >> 16U) & 1U;
    return status;
}

static struct cosmos_nvme_status cosmos_nvme_status_success(void) {
    return cosmos_nvme_status_from_policy(
        cosmos_nvme_media_policy_status_success());
}

static struct cosmos_nvme_status cosmos_nvme_status_invalid_opcode(void) {
    return cosmos_nvme_status_from_policy(
        cosmos_nvme_media_policy_status_invalid_opcode());
}

static struct cosmos_nvme_status cosmos_nvme_io_validate(
    const struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command, unsigned int *block_count) {
    *block_count = command->nlb + 1U;
    return cosmos_nvme_status_from_policy(cosmos_nvme_media_policy_rw_status(
        command->cid, command->namespace_id, command->lba_low,
        command->lba_high, command->nlb, command->control,
        command->data_address_low, command->data_address_high,
        command->data_address2_low, command->data_address2_high,
        command->data_bytes, service->namespace_blocks_low,
        service->namespace_blocks_high, service->block_bytes));
}

static int cosmos_nvme_status_is_success(struct cosmos_nvme_status status) {
    return cosmos_nvme_media_policy_status_is_success(
        (status.dnr << 16U) | (status.sct << 8U) | status.sc);
}

static struct cosmos_nvme_status cosmos_nvme_media_status(
    int result, unsigned int media_sc) {
    return cosmos_nvme_status_from_policy(
        cosmos_nvme_media_policy_media_status(result, media_sc));
}

static struct cosmos_nvme_status cosmos_nvme_execute(
    struct cosmos_nvme_service *service,
    const struct cosmos_nvme_command *command) {
    unsigned int block_count;
    struct cosmos_nvme_status status;
    int result;

    if (command->opcode == COSMOS_NVME_OPCODE_FLUSH) {
        status = cosmos_nvme_status_from_policy(
            cosmos_nvme_media_policy_flush_status(
                command->cid, command->namespace_id, command->lba_low,
                command->lba_high, command->nlb,
                command->data_address_low, command->data_address_high,
                command->data_address2_low, command->data_address2_high,
                command->data_bytes));
        if (!cosmos_nvme_status_is_success(status)) {
            return status;
        }
        return cosmos_nvme_media_status(
            service->adapter.media_flush(service->adapter.context),
            COSMOS_NVME_SC_WRITE_FAULT);
    }
    if (command->opcode == COSMOS_NVME_OPCODE_WRITE_ZEROES) {
        status = cosmos_nvme_status_from_policy(
            cosmos_nvme_media_policy_zeroes_status(
                command->cid, command->namespace_id, command->lba_low,
                command->lba_high, command->nlb, command->control,
                command->dataset_attributes, command->dataset_range_count,
                command->data_address_low, command->data_address_high,
                command->data_address2_low, command->data_address2_high,
                command->data_bytes, service->namespace_blocks_low,
                service->namespace_blocks_high,
                service->adapter.media_write_zeroes != 0 ? 1U : 0U));
        if (!cosmos_nvme_status_is_success(status)) {
            return status;
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
        status = cosmos_nvme_status_from_policy(
            cosmos_nvme_media_policy_dsm_status(
                command->cid, command->namespace_id, command->lba_low,
                command->lba_high, command->nlb, command->control,
                command->dataset_attributes, command->dataset_range_count,
                command->data_address_low, command->data_address_high,
                command->data_address2_low, command->data_address2_high,
                command->data_bytes,
                service->adapter.media_deallocate != 0 ? 1U : 0U));
        if (!cosmos_nvme_status_is_success(status)) {
            return status;
        }
        if ((command->dataset_attributes &
             COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE) == 0U) {
            return cosmos_nvme_status_success();
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
    int policy_status = cosmos_nvme_media_policy_post_status(
        (unsigned int)result);

    service->completion_state = (enum cosmos_nvme_completion_state)
        cosmos_nvme_media_policy_post_state((unsigned int)result);
    if (policy_status == COSMOS_OK) {
        service->completion_terminal_status = COSMOS_OK;
        return COSMOS_OK;
    }
    if (policy_status == COSMOS_RETRY) {
        return COSMOS_RETRY;
    }
    service->completion_terminal_status = policy_status;
    return policy_status;
}

int cosmos_nvme_service_init(struct cosmos_nvme_service *service,
                             const struct cosmos_nvme_adapter *adapter,
                             unsigned int namespace_blocks_low,
                             unsigned int namespace_blocks_high,
                             unsigned int block_bytes) {
    if (service == 0 || adapter == 0 ||
        !cosmos_nvme_media_policy_service_init_valid(
            adapter != 0 && adapter->post_completion != 0 ? 1U : 0U,
            adapter != 0 && adapter->media_read != 0 ? 1U : 0U,
            adapter != 0 && adapter->media_program != 0 ? 1U : 0U,
            adapter != 0 && adapter->media_flush != 0 ? 1U : 0U,
            namespace_blocks_low, namespace_blocks_high, block_bytes)) {
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
