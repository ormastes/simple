#include "cosmos_nvme_admin.h"
#include "cosmos_nvme_admin_policy.h"

/* ABI conversion only; all status selection is owned by pure Simple. */
static struct cosmos_nvme_status status_from_policy(unsigned int encoded) {
    struct cosmos_nvme_status status;

    status.sct = (encoded >> 8U) & 0xFFU;
    status.sc = encoded & 0xFFU;
    status.dnr = (encoded >> 16U) & 1U;
    return status;
}

static struct cosmos_nvme_status status_success(void) {
    return status_from_policy(cosmos_nvme_admin_policy_status_success());
}

static struct cosmos_nvme_status status_generic(unsigned int sc) {
    return status_from_policy(cosmos_nvme_admin_policy_status_generic(sc));
}

static void zero_bytes(unsigned char *bytes, unsigned int count) {
    unsigned int index;

    for (index = 0U; index < count; index++) {
        bytes[index] = 0U;
    }
}

static void put_le32(unsigned char *bytes, unsigned int value) {
    bytes[0] = (unsigned char)value;
    bytes[1] = (unsigned char)(value >> 8U);
    bytes[2] = (unsigned char)(value >> 16U);
    bytes[3] = (unsigned char)(value >> 24U);
}

static void put_le64(unsigned char *bytes, unsigned int low, unsigned int high) {
    put_le32(bytes, low);
    put_le32(bytes + 4U, high);
}

static int payload_valid(const struct cosmos_nvme_admin_command *command,
                         unsigned int bytes) {
    return cosmos_nvme_admin_policy_payload_valid(
        command->payload_address_low, command->payload_address_high,
        command->payload_address2_low, command->payload_address2_high,
        command->payload_bytes, bytes);
}

static void completion_from_command(
    struct cosmos_nvme_admin_completion *completion,
    const struct cosmos_nvme_admin_command *command,
    struct cosmos_nvme_status status, unsigned int result_low) {
    completion->queue_id = command->queue_id;
    completion->slot_tag = command->slot_tag;
    completion->sequence = command->sequence;
    completion->cid = command->cid;
    completion->result_low = result_low;
    completion->result_high = 0U;
    completion->status = status;
}

static int publish_pending(struct cosmos_nvme_admin_service *service) {
    enum cosmos_nvme_post_result result = service->adapter.post_completion(
        service->adapter.context, &service->pending_completion);
    int policy_result = cosmos_nvme_admin_policy_publish_result(
        (unsigned int)result);

    service->completion_state = (enum cosmos_nvme_completion_state)
        cosmos_nvme_admin_policy_publish_state((unsigned int)result);
    if (policy_result == COSMOS_OK) {
        service->completion_terminal_status = COSMOS_OK;
        return COSMOS_OK;
    }
    if (policy_result == COSMOS_RETRY) {
        return COSMOS_RETRY;
    }
    service->completion_terminal_status = policy_result;
    return service->completion_terminal_status;
}

static struct cosmos_nvme_status write_payload(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int bytes) {
    enum cosmos_nvme_admin_payload_result result;

    if (!payload_valid(command, bytes)) {
        return status_from_policy(cosmos_nvme_admin_policy_payload_status(
            0U, COSMOS_NVME_ADMIN_PAYLOAD_NOT_COMMITTED));
    }
    result = service->adapter.write_payload(
        service->adapter.context, command, service->payload, bytes);
    return status_from_policy(cosmos_nvme_admin_policy_payload_status(
        1U, (unsigned int)result));
}

static struct cosmos_nvme_status identify(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int cns = command->cdw10 & 0xFFU;
    unsigned int policy_status = cosmos_nvme_admin_policy_identify_status(
        command->namespace_id, command->cdw10, command->cdw11,
        command->cdw12, command->cdw13);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    zero_bytes(service->payload, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    if (cns == COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER) {
        service->payload[512U] = 0x66U; /* SQES: min/max 64-byte entries. */
        service->payload[513U] = 0x44U; /* CQES: min/max 16-byte entries. */
        service->payload[77U] = 8U; /* 4 KiB * 2^8 = 1 MiB AUTO DMA. */
        put_le32(service->payload + 516U, COSMOS_NVME_NAMESPACE_ID);
        service->payload[520U] = 0x0CU; /* ONCS: DSM and Write Zeroes. */
        return write_payload(service, command, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    }
    put_le64(service->payload, service->namespace_blocks_low,
             service->namespace_blocks_high);
    put_le64(service->payload + 8U, service->namespace_blocks_low,
             service->namespace_blocks_high);
    put_le64(service->payload + 16U, service->namespace_blocks_low,
             service->namespace_blocks_high);
    service->payload[25U] = 0U; /* One LBA format, indexed by FLBAS=0. */
    service->payload[130U] = (unsigned char)cosmos_nvme_admin_policy_log2(
        service->block_bytes);
    return write_payload(service, command, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
}

static struct cosmos_nvme_status get_log_page(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int policy_status = cosmos_nvme_admin_policy_get_log_status(
        command->namespace_id, command->cdw10, command->cdw11,
        command->cdw12, command->cdw13);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    zero_bytes(service->payload, COSMOS_NVME_ADMIN_SMART_BYTES);
    return write_payload(service, command, COSMOS_NVME_ADMIN_SMART_BYTES);
}

static struct cosmos_nvme_status set_features(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    unsigned int policy_status = cosmos_nvme_admin_policy_set_features_status(
        command->namespace_id, command->cdw10, command->cdw11,
        command->cdw12, command->cdw13);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    service->negotiated_queue_count =
        cosmos_nvme_admin_policy_queue_count(command->cdw11);
    *result = cosmos_nvme_admin_policy_queue_result(
        service->negotiated_queue_count);
    return status_success();
}

static struct cosmos_nvme_status get_features(
    const struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    unsigned int policy_status = cosmos_nvme_admin_policy_get_features_status(
        command->namespace_id, command->cdw10, command->cdw11,
        command->cdw12, command->cdw13);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    *result = cosmos_nvme_admin_policy_queue_result(
        service->negotiated_queue_count);
    return status_success();
}

static struct cosmos_nvme_status create_cq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int queue_id = command->cdw10 & 0xFFFFU;
    unsigned int entries = (command->cdw10 >> 16U) + 1U;
    unsigned int index = queue_id > 0U &&
        queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ? queue_id - 1U : 0U;
    unsigned int policy_status = cosmos_nvme_admin_policy_create_cq_status(
        service->negotiated_queue_count,
        service->completion_queues[index].valid, command->namespace_id,
        command->cdw10, command->cdw11, command->cdw12, command->cdw13,
        command->payload_address_low, command->payload_address_high,
        command->payload_address2_low, command->payload_address2_high,
        command->payload_bytes);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    if (service->adapter.configure_io_cq != 0 &&
        service->adapter.configure_io_cq(
            service->adapter.context, queue_id, 1U,
            (command->cdw11 >> 1U) & 1U, command->cdw11 >> 16U,
            entries, command->payload_address_low,
            command->payload_address_high) != COSMOS_OK) {
        return status_from_policy(
            cosmos_nvme_admin_policy_adapter_failure_status(COSMOS_HW_ERROR));
    }
    service->completion_queues[index].entries = entries;
    service->completion_queues[index].completion_queue_id = 0U;
    service->completion_queues[index].valid = 1U;
    return status_success();
}

static struct cosmos_nvme_status create_sq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int queue_id = command->cdw10 & 0xFFFFU;
    unsigned int entries = (command->cdw10 >> 16U) + 1U;
    unsigned int completion_queue_id = command->cdw11 >> 16U;
    unsigned int index = queue_id > 0U &&
        queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ? queue_id - 1U : 0U;
    unsigned int completion_index = completion_queue_id > 0U &&
        completion_queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ?
        completion_queue_id - 1U : 0U;
    unsigned int policy_status = cosmos_nvme_admin_policy_create_sq_status(
        service->negotiated_queue_count,
        service->completion_queues[completion_index].valid,
        service->submission_queues[index].valid, command->namespace_id,
        command->cdw10, command->cdw11, command->cdw12, command->cdw13,
        command->payload_address_low, command->payload_address_high,
        command->payload_address2_low, command->payload_address2_high,
        command->payload_bytes);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    if (service->adapter.configure_io_sq != 0 &&
        service->adapter.configure_io_sq(
            service->adapter.context, queue_id, 1U,
            completion_queue_id, entries, command->payload_address_low,
            command->payload_address_high) != COSMOS_OK) {
        return status_from_policy(
            cosmos_nvme_admin_policy_adapter_failure_status(COSMOS_HW_ERROR));
    }
    service->submission_queues[index].entries = entries;
    service->submission_queues[index].completion_queue_id = completion_queue_id;
    service->submission_queues[index].valid = 1U;
    return status_success();
}

static struct cosmos_nvme_status delete_sq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int queue_id = command->cdw10 & 0xFFFFU;
    unsigned int index = queue_id > 0U &&
        queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ? queue_id - 1U : 0U;
    unsigned int policy_status = cosmos_nvme_admin_policy_delete_sq_status(
        service->negotiated_queue_count,
        service->submission_queues[index].valid, command->namespace_id,
        command->cdw10, command->cdw11, command->cdw12, command->cdw13,
        command->payload_address_low, command->payload_address_high,
        command->payload_address2_low, command->payload_address2_high,
        command->payload_bytes);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    if (service->adapter.configure_io_sq != 0 &&
        service->adapter.configure_io_sq(
            service->adapter.context, index + 1U, 0U, 0U, 0U, 0U, 0U) !=
            COSMOS_OK) {
        return status_from_policy(
            cosmos_nvme_admin_policy_adapter_failure_status(COSMOS_HW_ERROR));
    }
    service->submission_queues[index].valid = 0U;
    return status_success();
}

static struct cosmos_nvme_status delete_cq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int queue_id = command->cdw10 & 0xFFFFU;
    unsigned int index = queue_id > 0U &&
        queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ? queue_id - 1U : 0U;
    unsigned int scan;
    unsigned int has_dependent_sq = 0U;
    unsigned int policy_status;

    for (scan = 0U; scan < COSMOS_NVME_ADMIN_MAX_IO_QUEUES; scan++) {
        if (service->submission_queues[scan].valid != 0U &&
            service->submission_queues[scan].completion_queue_id ==
                (index + 1U)) {
            has_dependent_sq = 1U;
        }
    }
    policy_status = cosmos_nvme_admin_policy_delete_cq_status(
        service->negotiated_queue_count,
        service->completion_queues[index].valid, has_dependent_sq,
        command->namespace_id, command->cdw10, command->cdw11,
        command->cdw12, command->cdw13, command->payload_address_low,
        command->payload_address_high, command->payload_address2_low,
        command->payload_address2_high, command->payload_bytes);
    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    if (service->adapter.configure_io_cq != 0 &&
        service->adapter.configure_io_cq(
            service->adapter.context, index + 1U, 0U, 0U, 0U, 0U, 0U, 0U) !=
            COSMOS_OK) {
        return status_from_policy(
            cosmos_nvme_admin_policy_adapter_failure_status(COSMOS_HW_ERROR));
    }
    service->completion_queues[index].valid = 0U;
    return status_success();
}

static struct cosmos_nvme_status abort_command(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    unsigned int target_cid = command->cdw10 & 0xFFFFU;
    unsigned int target_queue_id = command->cdw10 >> 16U;
    unsigned int index = target_queue_id > 0U &&
        target_queue_id <= COSMOS_NVME_ADMIN_MAX_IO_QUEUES ?
        target_queue_id - 1U : 0U;
    unsigned int policy_status = cosmos_nvme_admin_policy_abort_status(
        service->negotiated_queue_count,
        service->submission_queues[index].valid, command->namespace_id,
        command->cdw10, command->cdw11, command->cdw12, command->cdw13);

    if (policy_status != cosmos_nvme_admin_policy_status_success()) {
        return status_from_policy(policy_status);
    }
    *result = cosmos_nvme_admin_policy_abort_result(
        target_queue_id, target_cid, service->async_event_pending,
        service->pending_async_event.cid);
    if (*result == 0U) {
        service->async_event_pending = 0U;
    }
    return status_success();
}

static int execute_command(struct cosmos_nvme_admin_service *service,
                           const struct cosmos_nvme_admin_command *command,
                           struct cosmos_nvme_status *status,
                           unsigned int *result_low) {
    unsigned int policy_status;

    *result_low = 0U;
    policy_status = cosmos_nvme_admin_policy_envelope_status(
        command->invalid_field, command->queue_id, command->cid,
        command->opcode, command->payload_address_low,
        command->payload_address_high, command->payload_address2_low,
        command->payload_address2_high, command->payload_bytes);
    if (policy_status != COSMOS_NVME_ADMIN_POLICY_CONTINUE) {
        *status = status_from_policy(policy_status);
        return 0;
    }
    switch (command->opcode) {
    case COSMOS_NVME_ADMIN_IDENTIFY:
        *status = identify(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_GET_LOG_PAGE:
        *status = get_log_page(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_SET_FEATURES:
        *status = set_features(service, command, result_low);
        return 0;
    case COSMOS_NVME_ADMIN_GET_FEATURES:
        *status = get_features(service, command, result_low);
        return 0;
    case COSMOS_NVME_ADMIN_CREATE_IO_CQ:
        *status = create_cq(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_CREATE_IO_SQ:
        *status = create_sq(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_DELETE_IO_SQ:
        *status = delete_sq(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_DELETE_IO_CQ:
        *status = delete_cq(service, command);
        return 0;
    case COSMOS_NVME_ADMIN_ABORT:
        *status = abort_command(service, command, result_low);
        return 0;
    case COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST:
        policy_status = cosmos_nvme_admin_policy_async_event_status(
            service->adapter.poll_async_event != 0 ? 1U : 0U,
            service->async_event_pending, command->namespace_id,
            command->cdw10, command->cdw11, command->cdw12, command->cdw13);
        if (policy_status == COSMOS_NVME_ADMIN_POLICY_CONTINUE) {
            service->pending_async_event = *command;
            service->async_event_pending = 1U;
            return 1;
        }
        *status = status_from_policy(policy_status);
        return 0;
    default:
        *status = status_generic(COSMOS_NVME_SC_INVALID_OPCODE);
        return 0;
    }
}

static int service_async_event(struct cosmos_nvme_admin_service *service) {
    unsigned int result_low;
    int result;

    if (service->async_event_pending == 0U) {
        return COSMOS_OK;
    }
    result = service->adapter.poll_async_event(service->adapter.context,
                                                &result_low);
    if (result == COSMOS_UNAVAILABLE) {
        return COSMOS_OK;
    }
    if (result != COSMOS_OK) {
        return result;
    }
    completion_from_command(&service->pending_completion,
                            &service->pending_async_event, status_success(),
                            result_low);
    service->async_event_pending = 0U;
    service->completion_state = COSMOS_NVME_COMPLETION_RETRY;
    return publish_pending(service);
}

int cosmos_nvme_admin_init(struct cosmos_nvme_admin_service *service,
                           const struct cosmos_nvme_admin_adapter *adapter,
                           unsigned int namespace_blocks_low,
                           unsigned int namespace_blocks_high,
                           unsigned int block_bytes) {
    unsigned int index;

    if (service == 0 || adapter == 0 || adapter->post_completion == 0 ||
        adapter->write_payload == 0 ||
        !cosmos_nvme_admin_policy_init_values_valid(
            namespace_blocks_low, namespace_blocks_high, block_bytes)) {
        return COSMOS_INVALID;
    }
    service->adapter = *adapter;
    service->namespace_blocks_low = namespace_blocks_low;
    service->namespace_blocks_high = namespace_blocks_high;
    service->block_bytes = block_bytes;
    service->negotiated_queue_count = COSMOS_NVME_ADMIN_MAX_IO_QUEUES;
    service->completion_state = COSMOS_NVME_COMPLETION_NONE;
    service->completion_terminal_status = COSMOS_OK;
    service->async_event_pending = 0U;
    for (index = 0U; index < COSMOS_NVME_ADMIN_MAX_IO_QUEUES; index++) {
        service->completion_queues[index].valid = 0U;
        service->submission_queues[index].valid = 0U;
    }
    return COSMOS_OK;
}

int cosmos_nvme_admin_accept(struct cosmos_nvme_admin_service *service,
                             const struct cosmos_nvme_admin_command *command) {
    struct cosmos_nvme_status status;
    unsigned int result_low;
    int deferred;
    int result;

    if (service == 0 || command == 0) {
        return COSMOS_INVALID;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_BLOCKED) {
        return service->completion_terminal_status;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_RETRY) {
        result = publish_pending(service);
        if (result != COSMOS_OK) {
            return result;
        }
    }
    deferred = execute_command(service, command, &status, &result_low);
    if (deferred != 0) {
        return COSMOS_OK;
    }
    completion_from_command(&service->pending_completion, command, status,
                            result_low);
    service->completion_state = COSMOS_NVME_COMPLETION_RETRY;
    return publish_pending(service);
}

int cosmos_nvme_admin_poll(struct cosmos_nvme_admin_service *service) {
    unsigned int processed;
    int result;

    if (service == 0) {
        return COSMOS_INVALID;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_BLOCKED) {
        return service->completion_terminal_status;
    }
    if (service->completion_state == COSMOS_NVME_COMPLETION_RETRY) {
        result = publish_pending(service);
        if (result != COSMOS_OK) {
            return result;
        }
    }
    result = service_async_event(service);
    if (result != COSMOS_OK) {
        return result;
    }
    if (service->adapter.fetch_command == 0) {
        return COSMOS_OK;
    }
    for (processed = 0U; processed < COSMOS_NVME_ADMIN_SERVICE_BUDGET;
         processed++) {
        struct cosmos_nvme_admin_command command;
        result = service->adapter.fetch_command(service->adapter.context,
                                                &command);
        if (result == COSMOS_UNAVAILABLE) {
            return COSMOS_OK;
        }
        if (result != COSMOS_OK) {
            return result;
        }
        result = cosmos_nvme_admin_accept(service, &command);
        if (result != COSMOS_OK) {
            return result;
        }
    }
    return COSMOS_OK;
}
