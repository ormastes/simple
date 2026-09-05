#include <stdio.h>
#include <string.h>

#include "cosmos_nvme_admin.h"

#define CHECK(condition) do { if (!(condition)) { \
    fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #condition); \
    return 1; } } while (0)

#define TEST_CAPACITY 24U

struct mock_adapter {
    struct cosmos_nvme_admin_command commands[TEST_CAPACITY];
    struct cosmos_nvme_admin_completion completions[TEST_CAPACITY];
    enum cosmos_nvme_post_result post_results[TEST_CAPACITY];
    unsigned char payload[2U][COSMOS_NVME_ADMIN_IDENTIFY_BYTES];
    unsigned int command_count;
    unsigned int fetch_index;
    unsigned int completion_count;
    unsigned int post_index;
    unsigned int post_count;
    unsigned int payload_count;
    unsigned int payload_address_low;
    unsigned int payload_address_high;
    unsigned int payload_bytes;
    unsigned int sq_config_count;
    unsigned int cq_config_count;
    unsigned int event_result;
    int event_status;
    enum cosmos_nvme_admin_payload_result payload_result;
};

static void reset(struct mock_adapter *mock) {
    memset(mock, 0, sizeof(*mock));
    mock->event_status = COSMOS_UNAVAILABLE;
    mock->payload_result = COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED;
}

static int fetch(void *context, struct cosmos_nvme_admin_command *command) {
    struct mock_adapter *mock = context;
    if (mock->fetch_index == mock->command_count) return COSMOS_UNAVAILABLE;
    *command = mock->commands[mock->fetch_index++];
    return COSMOS_OK;
}

static enum cosmos_nvme_post_result post(
    void *context, const struct cosmos_nvme_admin_completion *completion) {
    struct mock_adapter *mock = context;
    enum cosmos_nvme_post_result result = COSMOS_NVME_POST_COMMITTED;
    if (mock->post_index < mock->post_count) result = mock->post_results[mock->post_index++];
    if (result == COSMOS_NVME_POST_COMMITTED) mock->completions[mock->completion_count++] = *completion;
    return result;
}

static enum cosmos_nvme_admin_payload_result payload(
    void *context, const struct cosmos_nvme_admin_command *command,
    const unsigned char *bytes,
    unsigned int count) {
    struct mock_adapter *mock = context;
    unsigned int payload_index = mock->payload_count++;
    mock->payload_address_low = command->payload_address_low;
    mock->payload_address_high = command->payload_address_high;
    mock->payload_bytes = count;
    if (mock->payload_result == COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED &&
        payload_index < 2U) {
        memcpy(mock->payload[payload_index], bytes, count);
    }
    return mock->payload_result;
}

static int event(void *context, unsigned int *result_low) {
    struct mock_adapter *mock = context;
    *result_low = mock->event_result;
    return mock->event_status;
}

static int configure_sq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    struct mock_adapter *mock = context;

    (void)queue_id;
    (void)valid;
    (void)completion_queue_id;
    (void)entries;
    (void)address_low;
    (void)address_high;
    mock->sq_config_count++;
    return COSMOS_OK;
}

static int configure_cq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    struct mock_adapter *mock = context;

    (void)queue_id;
    (void)valid;
    (void)irq_enable;
    (void)irq_vector;
    (void)entries;
    (void)address_low;
    (void)address_high;
    mock->cq_config_count++;
    return COSMOS_OK;
}

static int init(struct cosmos_nvme_admin_service *service, struct mock_adapter *mock) {
    const struct cosmos_nvme_admin_adapter adapter = {
        mock, fetch, post, payload, event, configure_sq, configure_cq
    };
    return cosmos_nvme_admin_init(service, &adapter, 0x1000U, 0U, 512U);
}

static struct cosmos_nvme_admin_command command(unsigned int cid, unsigned int opcode) {
    struct cosmos_nvme_admin_command value;
    memset(&value, 0, sizeof(value));
    value.slot_tag = 0x100U + cid;
    value.sequence = 0x1000U + cid;
    value.cid = cid;
    value.opcode = opcode;
    if (opcode == COSMOS_NVME_ADMIN_CREATE_IO_SQ ||
        opcode == COSMOS_NVME_ADMIN_CREATE_IO_CQ) {
        value.payload_address_low = 0x01000000U + cid * 0x1000U;
    }
    return value;
}

static void payload_command(struct cosmos_nvme_admin_command *value, unsigned int bytes) {
    value->payload_address_low = 0x00200000U;
    value->payload_address_high = 0x12345678U;
    value->payload_bytes = bytes;
}

static int completion(const struct cosmos_nvme_admin_completion *value,
                      unsigned int cid, unsigned int sct, unsigned int sc,
                      unsigned int dnr) {
    return value->queue_id == 0U && value->slot_tag == 0x100U + cid &&
        value->sequence == 0x1000U + cid && value->cid == cid &&
        value->status.sct == sct && value->status.sc == sc &&
        value->status.dnr == dnr;
}

static int test_identify_and_payload_contract(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(1U, COSMOS_NVME_ADMIN_IDENTIFY);
    mock.commands[0].cdw10 = COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER;
    payload_command(&mock.commands[0], COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    mock.commands[1] = command(2U, COSMOS_NVME_ADMIN_IDENTIFY);
    mock.commands[1].namespace_id = COSMOS_NVME_NAMESPACE_ID;
    payload_command(&mock.commands[1], COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    mock.command_count = 2U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(mock.payload_count == 2U && mock.payload_bytes == COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    CHECK(completion(&mock.completions[0], 1U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[1], 2U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.payload[0][512] == 0x66U && mock.payload[0][513] == 0x44U);
    CHECK(mock.payload[0][77] == 8U);
    CHECK(mock.payload[0][520] == 0x0CU);
    CHECK(mock.payload[1][0] == 0x00U && mock.payload[1][1] == 0x10U);
    CHECK(mock.payload[1][128] == 0x00U && mock.payload[1][130] == 9U);
    return 0;
}

static int test_malformed_and_payload_failure(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(3U, COSMOS_NVME_ADMIN_IDENTIFY);
    mock.commands[0].cdw10 = COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER;
    payload_command(&mock.commands[0], 512U);
    mock.commands[1] = command(4U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[1].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[1].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (127U << 16U);
    payload_command(&mock.commands[1], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.payload_result = COSMOS_NVME_ADMIN_PAYLOAD_NOT_COMMITTED;
    mock.command_count = 2U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(completion(&mock.completions[0], 3U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(completion(&mock.completions[1], 4U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(mock.payload_count == 1U);
    return 0;
}

static int test_queue_lifecycle_and_feature_floor(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(5U, COSMOS_NVME_ADMIN_SET_FEATURES);
    mock.commands[0].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.commands[0].cdw11 = (9U << 16U) | 9U;
    mock.commands[1] = command(6U, COSMOS_NVME_ADMIN_CREATE_IO_SQ);
    mock.commands[1].cdw10 = 1U;
    mock.commands[1].cdw11 = 1U | (1U << 16U);
    mock.commands[2] = command(7U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[2].cdw10 = 1U;
    mock.commands[2].cdw11 = 3U;
    mock.commands[3] = command(8U, COSMOS_NVME_ADMIN_CREATE_IO_SQ);
    mock.commands[3].cdw10 = 1U;
    mock.commands[3].cdw11 = 1U | (1U << 16U);
    mock.commands[4] = command(9U, COSMOS_NVME_ADMIN_DELETE_IO_CQ);
    mock.commands[4].cdw10 = 1U;
    mock.commands[5] = command(10U, COSMOS_NVME_ADMIN_DELETE_IO_SQ);
    mock.commands[5].cdw10 = 1U;
    mock.commands[6] = command(11U, COSMOS_NVME_ADMIN_DELETE_IO_CQ);
    mock.commands[6].cdw10 = 1U;
    mock.commands[7] = command(12U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[7].cdw10 = 5U;
    mock.commands[7].cdw11 = 1U;
    mock.command_count = 8U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(completion(&mock.completions[0], 5U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.completions[0].result_low == 0x00030003U);
    CHECK(completion(&mock.completions[1], 6U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_COMPLETION_QUEUE_INVALID, 1U));
    CHECK(completion(&mock.completions[2], 7U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[3], 8U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[4], 9U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_DELETION, 1U));
    CHECK(completion(&mock.completions[5], 10U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[6], 11U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[7], 12U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_INVALID_QUEUE_IDENTIFIER, 1U));
    return 0;
}

static int test_feature_namespace_and_queue_field_edges(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(20U, COSMOS_NVME_ADMIN_SET_FEATURES);
    mock.commands[0].namespace_id = COSMOS_NVME_NAMESPACE_ID;
    mock.commands[0].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.commands[0].cdw11 = (0xFFFEU << 16U) | 0xFFFEU;
    mock.commands[1] = command(21U, COSMOS_NVME_ADMIN_GET_FEATURES);
    mock.commands[1].namespace_id = COSMOS_NVME_NAMESPACE_ID;
    mock.commands[1].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.commands[2] = command(22U, COSMOS_NVME_ADMIN_SET_FEATURES);
    mock.commands[2].namespace_id = 2U;
    mock.commands[2].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.commands[3] = command(23U, COSMOS_NVME_ADMIN_SET_FEATURES);
    mock.commands[3].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.commands[3].cdw11 = 0xFFFFU;
    mock.commands[4] = command(24U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[4].cdw10 = 1U;
    mock.commands[4].cdw11 = 3U;
    mock.commands[5] = command(25U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[5].cdw10 = 2U;
    mock.commands[5].cdw11 = 3U | (1U << 16U);
    mock.commands[6] = command(26U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[6].cdw10 = 2U;
    mock.commands[6].cdw11 = 1U | 4U;
    mock.commands[7] = command(27U, COSMOS_NVME_ADMIN_CREATE_IO_SQ);
    mock.commands[7].cdw10 = 1U;
    mock.commands[7].cdw11 = 1U | (3U << 1U) | (1U << 16U);
    mock.command_count = 8U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(completion(&mock.completions[0], 20U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.completions[0].result_low == 0x00030003U);
    CHECK(completion(&mock.completions[1], 21U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[2], 22U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT, 1U));
    CHECK(completion(&mock.completions[3], 23U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[4], 24U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[5], 25U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_INVALID_INTERRUPT_VECTOR, 1U));
    CHECK(completion(&mock.completions[6], 26U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[7], 27U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    return 0;
}

static int test_smart_global_namespace_and_request_edges(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(28U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[0].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[0].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (1U << 15U) |
        (127U << 16U);
    payload_command(&mock.commands[0], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[1] = command(29U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[1].namespace_id = COSMOS_NVME_NAMESPACE_ID;
    mock.commands[1].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (127U << 16U);
    payload_command(&mock.commands[1], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[2] = command(30U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[2].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (127U << 16U);
    payload_command(&mock.commands[2], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[3] = command(31U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[3].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[3].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (126U << 16U);
    payload_command(&mock.commands[3], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[4] = command(32U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[4].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[4].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (127U << 16U);
    mock.commands[4].cdw12 = 4U;
    payload_command(&mock.commands[4], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[5] = command(33U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[5].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[5].cdw10 = 3U | (127U << 16U);
    payload_command(&mock.commands[5], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.commands[6] = command(34U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[6].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[6].cdw10 = COSMOS_NVME_ADMIN_LOG_SMART_HEALTH | (127U << 16U);
    payload_command(&mock.commands[6], 256U);
    mock.command_count = 7U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(completion(&mock.completions[0], 28U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[1], 29U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion(&mock.completions[2], 30U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT, 1U));
    CHECK(completion(&mock.completions[3], 31U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[4], 32U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[5], 33U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_INVALID_LOG_PAGE, 1U));
    CHECK(completion(&mock.completions[6], 34U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    return 0;
}

static int test_queue_pc_and_interrupt_edges(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(35U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[0].cdw10 = 1U;
    mock.commands[1] = command(36U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    mock.commands[1].cdw10 = 1U;
    mock.commands[1].cdw11 = 1U | (1U << 16U);
    mock.commands[2] = command(37U, COSMOS_NVME_ADMIN_CREATE_IO_SQ);
    mock.commands[2].cdw10 = 1U;
    mock.commands[2].cdw11 = 1U << 16U;
    mock.command_count = 3U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(completion(&mock.completions[0], 35U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[1], 36U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion(&mock.completions[2], 37U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_FIELD, 1U));
    return 0;
}

static int test_statuses_aer_abort_and_no_loss(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    reset(&mock);
    mock.commands[0] = command(13U, 0xFFU);
    mock.commands[1] = command(14U, COSMOS_NVME_ADMIN_GET_FEATURES);
    mock.commands[1].namespace_id = 2U;
    mock.commands[2] = command(15U, COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST);
    mock.commands[3] = command(16U, COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST);
    mock.commands[4] = command(17U, COSMOS_NVME_ADMIN_ABORT);
    mock.commands[4].cdw10 = 15U;
    mock.commands[5] = command(18U, COSMOS_NVME_ADMIN_GET_LOG_PAGE);
    mock.commands[5].namespace_id = COSMOS_NVME_ADMIN_NAMESPACE_ALL;
    mock.commands[5].cdw10 = 3U | (127U << 16U);
    payload_command(&mock.commands[5], COSMOS_NVME_ADMIN_SMART_BYTES);
    mock.command_count = 6U;
    mock.post_results[0] = COSMOS_NVME_POST_NOT_COMMITTED_RETRY;
    mock.post_count = 1U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_RETRY);
    CHECK(mock.fetch_index == 1U);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(mock.fetch_index == 6U && mock.completion_count == 5U);
    CHECK(completion(&mock.completions[0], 13U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_OPCODE, 1U));
    CHECK(completion(&mock.completions[1], 14U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT, 1U));
    CHECK(completion(&mock.completions[2], 16U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_AER_LIMIT_EXCEEDED, 1U));
    CHECK(completion(&mock.completions[3], 17U, COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.completions[3].result_low == 0U);
    CHECK(completion(&mock.completions[4], 18U, COSMOS_NVME_SCT_COMMAND_SPECIFIC, COSMOS_NVME_ADMIN_SC_INVALID_LOG_PAGE, 1U));
    return 0;
}

static int test_aer_event_and_bounded_budget(void) {
    struct mock_adapter mock; struct cosmos_nvme_admin_service service;
    unsigned int index;
    unsigned int found = 0U;
    reset(&mock);
    mock.commands[0] = command(19U, COSMOS_NVME_ADMIN_ASYNC_EVENT_REQUEST);
    for (index = 1U; index < TEST_CAPACITY; index++) mock.commands[index] = command(19U + index, COSMOS_NVME_ADMIN_GET_FEATURES);
    for (index = 1U; index < TEST_CAPACITY; index++) mock.commands[index].cdw10 = COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    mock.command_count = TEST_CAPACITY;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(mock.fetch_index == COSMOS_NVME_ADMIN_SERVICE_BUDGET);
    mock.event_status = COSMOS_OK;
    mock.event_result = 0x00020001U;
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    for (index = 0U; index < mock.completion_count; index++) {
        if (mock.completions[index].cid == 19U &&
            mock.completions[index].result_low == 0x00020001U) found = 1U;
    }
    CHECK(found == 1U);
    return 0;
}

static int test_unsupported_format_and_firmware_guards(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_admin_service service;

    reset(&mock);
    mock.commands[0] = command(40U, COSMOS_NVME_ADMIN_FORMAT_NVM);
    mock.commands[1] = command(41U, COSMOS_NVME_ADMIN_FIRMWARE_COMMIT);
    mock.commands[2] = command(
        42U, COSMOS_NVME_ADMIN_FIRMWARE_IMAGE_DOWNLOAD);
    payload_command(&mock.commands[2], COSMOS_NVME_ADMIN_IDENTIFY_BYTES);
    mock.command_count = 3U;
    CHECK(init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_admin_poll(&service) == COSMOS_OK);
    CHECK(mock.completion_count == 3U);
    CHECK(mock.payload_count == 0U);
    CHECK(completion(&mock.completions[0], 40U, COSMOS_NVME_SCT_GENERIC,
                     COSMOS_NVME_SC_INVALID_OPCODE, 1U));
    CHECK(completion(&mock.completions[1], 41U, COSMOS_NVME_SCT_GENERIC,
                     COSMOS_NVME_SC_INVALID_OPCODE, 1U));
    CHECK(completion(&mock.completions[2], 42U, COSMOS_NVME_SCT_GENERIC,
                     COSMOS_NVME_SC_INVALID_OPCODE, 1U));
    return 0;
}

int main(void) {
    CHECK(test_identify_and_payload_contract() == 0);
    CHECK(test_malformed_and_payload_failure() == 0);
    CHECK(test_queue_lifecycle_and_feature_floor() == 0);
    CHECK(test_feature_namespace_and_queue_field_edges() == 0);
    CHECK(test_smart_global_namespace_and_request_edges() == 0);
    CHECK(test_queue_pc_and_interrupt_edges() == 0);
    CHECK(test_statuses_aer_abort_and_no_loss() == 0);
    CHECK(test_aer_event_and_bounded_budget() == 0);
    CHECK(test_unsupported_format_and_firmware_guards() == 0);
    puts("cosmos NVMe admin contract: PASS");
    return 0;
}
