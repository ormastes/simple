#include "cosmos_nvme_admin.h"

static struct cosmos_nvme_status status_make(unsigned int sct, unsigned int sc,
                                              unsigned int dnr) {
    struct cosmos_nvme_status status;

    status.sct = sct;
    status.sc = sc;
    status.dnr = dnr;
    return status;
}

static struct cosmos_nvme_status status_success(void) {
    return status_make(COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U);
}

static struct cosmos_nvme_status status_generic(unsigned int sc) {
    return status_make(COSMOS_NVME_SCT_GENERIC, sc, 1U);
}

static struct cosmos_nvme_status status_specific(unsigned int sc) {
    return status_make(COSMOS_NVME_SCT_COMMAND_SPECIFIC, sc, 1U);
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

static unsigned int min_unsigned(unsigned int left, unsigned int right) {
    return left < right ? left : right;
}

static int power_of_two(unsigned int value) {
    return value != 0U && (value & (value - 1U)) == 0U;
}

static unsigned int log2_unsigned(unsigned int value) {
    unsigned int result = 0U;

    while (value > 1U) {
        value >>= 1U;
        result++;
    }
    return result;
}

static int command_has_no_payload(const struct cosmos_nvme_admin_command *command) {
    return command->payload_address_low == 0U &&
        command->payload_address_high == 0U &&
        command->payload_address2_low == 0U &&
        command->payload_address2_high == 0U &&
        command->payload_bytes == 0U;
}

static int queue_base_valid(
    const struct cosmos_nvme_admin_command *command) {
    return command->payload_bytes == 0U &&
        command->payload_address2_low == 0U &&
        command->payload_address2_high == 0U &&
        (command->payload_address_low != 0U ||
         command->payload_address_high != 0U) &&
        (command->payload_address_low & 0xFFFU) == 0U &&
        command->payload_address_high <= 0xFU;
}

static int opcode_is_supported(unsigned int opcode) {
    switch (opcode) {
    case COSMOS_NVME_ADMIN_DELETE_IO_SQ:
    case COSMOS_NVME_ADMIN_CREATE_IO_SQ:
    case COSMOS_NVME_ADMIN_GET_LOG_PAGE:
    case COSMOS_NVME_ADMIN_DELETE_IO_CQ:
    case COSMOS_NVME_ADMIN_CREATE_IO_CQ:
    case COSMOS_NVME_ADMIN_IDENTIFY:
    case COSMOS_NVME_ADMIN_ABORT:
    case COSMOS_NVME_ADMIN_SET_FEATURES:
    case COSMOS_NVME_ADMIN_GET_FEATURES:
    case COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST:
        return 1;
    default:
        return 0;
    }
}

static int payload_valid(const struct cosmos_nvme_admin_command *command,
                         unsigned int bytes) {
    unsigned int first_room;
    unsigned int has_second;

    if (command->payload_bytes != bytes ||
        (command->payload_address_low == 0U &&
         command->payload_address_high == 0U) ||
        (command->payload_address_low & (COSMOS_NVME_DMA_ALIGNMENT - 1U)) !=
            0U) {
        return 0;
    }
    first_room = 4096U - (command->payload_address_low & 0xFFFU);
    has_second = command->payload_address2_low != 0U ||
        command->payload_address2_high != 0U;
    if (bytes <= first_room) {
        return has_second == 0U;
    }
    return has_second != 0U &&
        (command->payload_address2_low & 0xFFFU) == 0U;
}

static int queue_index(unsigned int queue_id, unsigned int *index) {
    if (queue_id == 0U || queue_id > COSMOS_NVME_ADMIN_MAX_IO_QUEUES) {
        return 0;
    }
    *index = queue_id - 1U;
    return 1;
}

static int queue_id_allowed(const struct cosmos_nvme_admin_service *service,
                            unsigned int queue_id, unsigned int *index) {
    return queue_id != 0U && queue_id <= service->negotiated_queue_count &&
        queue_index(queue_id, index);
}

static int controller_feature_namespace_valid(unsigned int namespace_id) {
    return namespace_id == 0U || namespace_id == COSMOS_NVME_NAMESPACE_ID;
}

static int smart_namespace_valid(unsigned int namespace_id) {
    return namespace_id == COSMOS_NVME_NAMESPACE_ID ||
        namespace_id == COSMOS_NVME_ADMIN_NAMESPACE_ALL;
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

    if (result == COSMOS_NVME_POST_COMMITTED) {
        service->completion_state = COSMOS_NVME_COMPLETION_NONE;
        service->completion_terminal_status = COSMOS_OK;
        return COSMOS_OK;
    }
    if (result == COSMOS_NVME_POST_NOT_COMMITTED_RETRY) {
        service->completion_state = COSMOS_NVME_COMPLETION_RETRY;
        return COSMOS_RETRY;
    }
    service->completion_state = COSMOS_NVME_COMPLETION_BLOCKED;
    service->completion_terminal_status =
        result == COSMOS_NVME_POST_AMBIGUOUS ? COSMOS_COMPLETION_UNCERTAIN :
        COSMOS_HW_ERROR;
    return service->completion_terminal_status;
}

static struct cosmos_nvme_status write_payload(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int bytes) {
    enum cosmos_nvme_admin_payload_result result;

    if (!payload_valid(command, bytes)) {
        return status_generic(COSMOS_NVME_SC_DATA_TRANSFER_ERROR);
    }
    result = service->adapter.write_payload(
        service->adapter.context, command, service->payload, bytes);
    if (result != COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED) {
        return status_generic(COSMOS_NVME_SC_DATA_TRANSFER_ERROR);
    }
    return status_success();
}

static struct cosmos_nvme_status identify(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int cns = command->cdw10 & 0xFFU;

    if ((command->cdw10 & ~0xFFU) != 0U || command->cdw11 != 0U ||
        command->cdw12 != 0U || command->cdw13 != 0U) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    zero_bytes(service->payload, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    if (cns == COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER) {
        if (command->namespace_id != 0U) {
            return status_generic(COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT);
        }
        service->payload[512U] = 0x66U; /* SQES: min/max 64-byte entries. */
        service->payload[513U] = 0x44U; /* CQES: min/max 16-byte entries. */
        service->payload[77U] = 8U; /* 4 KiB * 2^8 = 1 MiB AUTO DMA. */
        put_le32(service->payload + 516U, COSMOS_NVME_NAMESPACE_ID);
        service->payload[520U] = 0x0CU; /* ONCS: DSM and Write Zeroes. */
        return write_payload(service, command, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    }
    if (cns != COSMOS_NVME_ADMIN_IDENTIFY_NAMESPACE) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if (command->namespace_id != COSMOS_NVME_NAMESPACE_ID) {
        return status_generic(COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT);
    }
    put_le64(service->payload, service->namespace_blocks_low,
             service->namespace_blocks_high);
    put_le64(service->payload + 8U, service->namespace_blocks_low,
             service->namespace_blocks_high);
    put_le64(service->payload + 16U, service->namespace_blocks_low,
             service->namespace_blocks_high);
    service->payload[25U] = 0U; /* One LBA format, indexed by FLBAS=0. */
    service->payload[130U] = (unsigned char)log2_unsigned(service->block_bytes);
    return write_payload(service, command, COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
}

static struct cosmos_nvme_status get_log_page(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int lid = command->cdw10 & 0xFFU;
    unsigned int numd = (command->cdw10 >> 16U) & 0xFFFFU;

    if (!smart_namespace_valid(command->namespace_id)) {
        return status_generic(COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT);
    }
    if (lid != COSMOS_NVME_ADMIN_LOG_SMART_HEALTH) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_LOG_PAGE);
    }
    if ((command->cdw10 & 0x00007F00U) != 0U || numd != 127U ||
        command->cdw11 != 0U || command->cdw12 != 0U || command->cdw13 != 0U) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    zero_bytes(service->payload, COSMOS_NVME_ADMIN_SMART_BYTES);
    return write_payload(service, command, COSMOS_NVME_ADMIN_SMART_BYTES);
}

static struct cosmos_nvme_status set_features(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    unsigned int requested_cq;
    unsigned int requested_sq;

    if (!controller_feature_namespace_valid(command->namespace_id)) {
        return status_generic(COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT);
    }
    if ((command->cdw10 & 0x7FFFFF00U) != 0U || command->cdw12 != 0U ||
        command->cdw13 != 0U) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if ((command->cdw10 & 0xFFU) != COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if ((command->cdw10 & 0x80000000U) != 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_FEATURE_NOT_SAVEABLE);
    }
    if ((command->cdw11 & 0xFFFFU) == 0xFFFFU ||
        (command->cdw11 >> 16U) == 0xFFFFU) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    requested_sq = (command->cdw11 & 0xFFFFU) + 1U;
    requested_cq = (command->cdw11 >> 16U) + 1U;
    service->negotiated_queue_count = min_unsigned(
        COSMOS_NVME_ADMIN_MAX_IO_QUEUES,
        min_unsigned(requested_sq, requested_cq));
    *result = (service->negotiated_queue_count - 1U) |
        ((service->negotiated_queue_count - 1U) << 16U);
    return status_success();
}

static struct cosmos_nvme_status get_features(
    const struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    if (!controller_feature_namespace_valid(command->namespace_id)) {
        return status_generic(COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT);
    }
    if ((command->cdw10 & ~0x000007FFU) != 0U ||
        (command->cdw10 & 0xFFU) != COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES ||
        ((command->cdw10 >> 8U) & 0x7U) != 0U || command->cdw11 != 0U ||
        command->cdw12 != 0U || command->cdw13 != 0U) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    *result = (service->negotiated_queue_count - 1U) |
        ((service->negotiated_queue_count - 1U) << 16U);
    return status_success();
}

static struct cosmos_nvme_status create_cq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int queue_id = command->cdw10 & 0xFFFFU;
    unsigned int entries = (command->cdw10 >> 16U) + 1U;
    unsigned int index;

    if (command->namespace_id != 0U || command->cdw12 != 0U ||
        command->cdw13 != 0U || !queue_base_valid(command)) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if (!queue_id_allowed(service, queue_id, &index)) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    if (entries == 0U || entries > COSMOS_NVME_ADMIN_MAX_QUEUE_ENTRIES) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_SIZE);
    }
    if ((command->cdw11 & 1U) == 0U ||
        (command->cdw11 & 0x0000FFFCU) != 0U ||
        ((command->cdw11 & 2U) == 0U && (command->cdw11 >> 16U) != 0U)) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if ((command->cdw11 & 2U) != 0U && (command->cdw11 >> 16U) != 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_INTERRUPT_VECTOR);
    }
    if (service->completion_queues[index].valid != 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    if (service->adapter.configure_io_cq != 0 &&
        service->adapter.configure_io_cq(
            service->adapter.context, queue_id, 1U,
            (command->cdw11 >> 1U) & 1U, command->cdw11 >> 16U,
            entries, command->payload_address_low,
            command->payload_address_high) != COSMOS_OK) {
        return status_generic(COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR);
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
    unsigned int index;
    unsigned int completion_index;

    if (command->namespace_id != 0U || command->cdw12 != 0U ||
        command->cdw13 != 0U || (command->cdw11 & 1U) == 0U ||
        (command->cdw11 & 0x0000FFF8U) != 0U ||
        !queue_base_valid(command)) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if (!queue_id_allowed(service, queue_id, &index) ||
        !queue_id_allowed(service, completion_queue_id, &completion_index)) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    if (entries == 0U || entries > COSMOS_NVME_ADMIN_MAX_QUEUE_ENTRIES) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_SIZE);
    }
    if (service->completion_queues[completion_index].valid == 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_COMPLETION_QUEUE_INVALID);
    }
    if (service->submission_queues[index].valid != 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    if (service->adapter.configure_io_sq != 0 &&
        service->adapter.configure_io_sq(
            service->adapter.context, queue_id, 1U,
            completion_queue_id, entries, command->payload_address_low,
            command->payload_address_high) != COSMOS_OK) {
        return status_generic(COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR);
    }
    service->submission_queues[index].entries = entries;
    service->submission_queues[index].completion_queue_id = completion_queue_id;
    service->submission_queues[index].valid = 1U;
    return status_success();
}

static struct cosmos_nvme_status delete_sq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int index;

    if (command->namespace_id != 0U || (command->cdw10 >> 16U) != 0U ||
        command->cdw11 != 0U || command->cdw12 != 0U || command->cdw13 != 0U ||
        !command_has_no_payload(command) ||
        !queue_id_allowed(service, command->cdw10 & 0xFFFFU, &index) ||
        service->submission_queues[index].valid == 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    if (service->adapter.configure_io_sq != 0 &&
        service->adapter.configure_io_sq(
            service->adapter.context, index + 1U, 0U, 0U, 0U, 0U, 0U) !=
            COSMOS_OK) {
        return status_generic(COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR);
    }
    service->submission_queues[index].valid = 0U;
    return status_success();
}

static struct cosmos_nvme_status delete_cq(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command) {
    unsigned int index;
    unsigned int scan;

    if (command->namespace_id != 0U || (command->cdw10 >> 16U) != 0U ||
        command->cdw11 != 0U || command->cdw12 != 0U || command->cdw13 != 0U ||
        !command_has_no_payload(command) ||
        !queue_id_allowed(service, command->cdw10 & 0xFFFFU, &index) ||
        service->completion_queues[index].valid == 0U) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    for (scan = 0U; scan < COSMOS_NVME_ADMIN_MAX_IO_QUEUES; scan++) {
        if (service->submission_queues[scan].valid != 0U &&
            service->submission_queues[scan].completion_queue_id ==
                (index + 1U)) {
            return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_DELETION);
        }
    }
    if (service->adapter.configure_io_cq != 0 &&
        service->adapter.configure_io_cq(
            service->adapter.context, index + 1U, 0U, 0U, 0U, 0U, 0U, 0U) !=
            COSMOS_OK) {
        return status_generic(COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR);
    }
    service->completion_queues[index].valid = 0U;
    return status_success();
}

static struct cosmos_nvme_status abort_command(
    struct cosmos_nvme_admin_service *service,
    const struct cosmos_nvme_admin_command *command, unsigned int *result) {
    unsigned int target_cid = command->cdw10 & 0xFFFFU;
    unsigned int target_queue_id = command->cdw10 >> 16U;
    unsigned int index;

    if (command->namespace_id != 0U || command->cdw11 != 0U ||
        command->cdw12 != 0U || command->cdw13 != 0U) {
        return status_generic(COSMOS_NVME_SC_INVALID_FIELD);
    }
    if (target_queue_id != 0U &&
        (!queue_id_allowed(service, target_queue_id, &index) ||
         service->submission_queues[index].valid == 0U)) {
        return status_specific(COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER);
    }
    *result = 1U;
    if (target_queue_id == 0U && service->async_event_pending != 0U &&
        service->pending_async_event.cid == target_cid) {
        service->async_event_pending = 0U;
        *result = 0U;
    }
    return status_success();
}

static int execute_command(struct cosmos_nvme_admin_service *service,
                           const struct cosmos_nvme_admin_command *command,
                           struct cosmos_nvme_status *status,
                           unsigned int *result_low) {
    *result_low = 0U;
    if (command->invalid_field != 0U || command->queue_id != 0U ||
        command->cid > COSMOS_NVME_MAX_CID) {
        *status = status_generic(COSMOS_NVME_SC_INVALID_FIELD);
        return 0;
    }
    if (!command_has_no_payload(command) &&
        opcode_is_supported(command->opcode) &&
        command->opcode != COSMOS_NVME_ADMIN_IDENTIFY &&
        command->opcode != COSMOS_NVME_ADMIN_GET_LOG_PAGE &&
        command->opcode != COSMOS_NVME_ADMIN_CREATE_IO_SQ &&
        command->opcode != COSMOS_NVME_ADMIN_CREATE_IO_CQ) {
        *status = status_generic(COSMOS_NVME_SC_INVALID_FIELD);
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
        if (service->adapter.poll_async_event == 0) {
            *status = status_generic(COSMOS_NVME_SC_INVALID_OPCODE);
        } else if (command->namespace_id != 0U || command->cdw10 != 0U ||
                   command->cdw11 != 0U || command->cdw12 != 0U ||
                   command->cdw13 != 0U) {
            *status = status_generic(COSMOS_NVME_SC_INVALID_FIELD);
        } else if (service->async_event_pending != 0U) {
            *status = status_specific(COSMOS_NVME_ADMIN_SC_AER_LIMIT_EXCEEDED);
        } else {
            service->pending_async_event = *command;
            service->async_event_pending = 1U;
            return 1;
        }
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
        (namespace_blocks_low == 0U && namespace_blocks_high == 0U) ||
        !power_of_two(block_bytes)) {
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
