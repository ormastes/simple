#include <stdio.h>
#include <string.h>

#include "cosmos_hal.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_COMMAND_CAPACITY (COSMOS_NVME_SERVICE_BUDGET + 3U)

/* This verifies the bounded adapter core only, not a PCIe or FTL binding. */
struct mock_adapter {
    struct cosmos_nvme_command commands[TEST_COMMAND_CAPACITY];
    struct cosmos_nvme_completion completions[TEST_COMMAND_CAPACITY];
    enum cosmos_nvme_post_result post_results[TEST_COMMAND_CAPACITY + 2U];
    unsigned int command_count;
    unsigned int fetch_index;
    unsigned int fetch_calls;
    unsigned int post_calls;
    unsigned int post_result_count;
    unsigned int post_result_index;
    unsigned int completion_count;
    unsigned int read_calls;
    unsigned int program_calls;
    unsigned int flush_calls;
    unsigned int zeroes_calls;
    unsigned int deallocate_calls;
    unsigned int last_lba_low;
    unsigned int last_lba_high;
    unsigned int last_block_count;
    unsigned int last_data_address_low;
    unsigned int last_data_address_high;
    unsigned int last_data_bytes;
    int read_status;
    int program_status;
    int flush_status;
};

static void mock_reset(struct mock_adapter *mock) {
    memset(mock, 0, sizeof(*mock));
    mock->read_status = COSMOS_OK;
    mock->program_status = COSMOS_OK;
    mock->flush_status = COSMOS_OK;
}

static int mock_fetch(void *context, struct cosmos_nvme_command *command) {
    struct mock_adapter *mock = context;

    mock->fetch_calls++;
    if (mock->fetch_index == mock->command_count) {
        return COSMOS_UNAVAILABLE;
    }
    *command = mock->commands[mock->fetch_index++];
    return COSMOS_OK;
}

static enum cosmos_nvme_post_result mock_post(
    void *context, const struct cosmos_nvme_completion *completion) {
    struct mock_adapter *mock = context;
    enum cosmos_nvme_post_result result = COSMOS_NVME_POST_COMMITTED;

    mock->post_calls++;
    if (mock->post_result_index < mock->post_result_count) {
        result = mock->post_results[mock->post_result_index++];
    }
    if (result == COSMOS_NVME_POST_COMMITTED) {
        mock->completions[mock->completion_count++] = *completion;
    }
    return result;
}

static int mock_read(
    void *context, const struct cosmos_nvme_command *command) {
    struct mock_adapter *mock = context;

    mock->read_calls++;
    mock->last_lba_low = command->lba_low;
    mock->last_lba_high = command->lba_high;
    mock->last_block_count = command->nlb + 1U;
    mock->last_data_address_low = command->data_address_low;
    mock->last_data_address_high = command->data_address_high;
    mock->last_data_bytes = command->data_bytes;
    return mock->read_status;
}

static int mock_program(
    void *context, const struct cosmos_nvme_command *command) {
    struct mock_adapter *mock = context;

    mock->program_calls++;
    mock->last_lba_low = command->lba_low;
    mock->last_lba_high = command->lba_high;
    mock->last_block_count = command->nlb + 1U;
    mock->last_data_address_low = command->data_address_low;
    mock->last_data_address_high = command->data_address_high;
    mock->last_data_bytes = command->data_bytes;
    return mock->program_status;
}

static int mock_flush(void *context) {
    struct mock_adapter *mock = context;

    mock->flush_calls++;
    return mock->flush_status;
}

static int mock_write_zeroes(
    void *context, const struct cosmos_nvme_command *command) {
    struct mock_adapter *mock = context;

    mock->zeroes_calls++;
    mock->last_lba_low = command->lba_low;
    mock->last_lba_high = command->lba_high;
    mock->last_block_count = command->nlb + 1U;
    return mock->program_status;
}

static int mock_deallocate(
    void *context, const struct cosmos_nvme_command *command) {
    struct mock_adapter *mock = context;

    mock->deallocate_calls++;
    mock->last_data_address_low = command->data_address_low;
    mock->last_data_address_high = command->data_address_high;
    mock->last_block_count = command->dataset_range_count;
    mock->last_data_bytes = command->data_bytes;
    return mock->program_status;
}

static int service_init_capacity(struct cosmos_nvme_service *service,
                                 struct mock_adapter *mock,
                                 unsigned int namespace_blocks_low,
                                 unsigned int namespace_blocks_high) {
    const struct cosmos_nvme_adapter adapter = {
        mock,
        mock_fetch,
        mock_post,
        mock_read,
        mock_program,
        mock_flush,
        mock_write_zeroes,
        mock_deallocate
    };

    return cosmos_nvme_service_init(
        service, &adapter, namespace_blocks_low, namespace_blocks_high, 512U);
}

static int service_init(struct cosmos_nvme_service *service,
                        struct mock_adapter *mock) {
    return service_init_capacity(service, mock, 128U, 0U);
}

static struct cosmos_nvme_command command(unsigned int id,
                                           unsigned int opcode) {
    struct cosmos_nvme_command value;

    memset(&value, 0, sizeof(value));
    value.queue_id = 0x20U + id;
    value.slot_tag = 0x100U + id;
    value.sequence = 0x1000U + id;
    value.cid = id;
    value.namespace_id = COSMOS_NVME_NAMESPACE_ID;
    value.opcode = opcode;
    if (opcode == COSMOS_NVME_OPCODE_READ ||
        opcode == COSMOS_NVME_OPCODE_WRITE) {
        value.data_address_low = 0x00200000U;
        value.data_address_high = 1U;
        value.data_bytes = 512U;
    }
    return value;
}

static int completion_is(const struct cosmos_nvme_completion *completion,
                         const struct cosmos_nvme_command *command,
                         unsigned int sct, unsigned int sc, unsigned int dnr) {
    return completion->queue_id == command->queue_id &&
        completion->slot_tag == command->slot_tag &&
        completion->sequence == command->sequence &&
        completion->cid == command->cid &&
        completion->status.sct == sct && completion->status.sc == sc &&
        completion->status.dnr == dnr;
}

static int test_empty_queue(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.fetch_calls == 1U);
    CHECK(mock.completion_count == 0U);
    return 0;
}

static int test_success_paths_preserve_identity_and_address(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.commands[0] = command(1U, COSMOS_NVME_OPCODE_READ);
    mock.commands[1] = command(2U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[1].lba_low = 7U;
    mock.commands[1].lba_high = 1U;
    mock.commands[1].nlb = 1U;
    mock.commands[1].data_bytes = 1024U;
    mock.commands[2] = command(3U, COSMOS_NVME_OPCODE_FLUSH);
    mock.command_count = 3U;
    CHECK(service_init_capacity(&service, &mock, 128U, 1U) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.flush_calls == 1U);
    CHECK(mock.completion_count == 3U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.last_lba_low == 7U);
    CHECK(mock.last_lba_high == 1U);
    CHECK(mock.last_block_count == 2U);
    CHECK(mock.last_data_address_high == 1U);
    CHECK(mock.last_data_address_low == 0x00200000U);
    CHECK(mock.last_data_bytes == 1024U);
    return 0;
}

static int test_status_mapping_and_no_media(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.commands[0] = command(4U, 0xFFU);
    mock.commands[1] = command(5U, COSMOS_NVME_OPCODE_READ);
    mock.commands[1].namespace_id = 2U;
    mock.commands[2] = command(6U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[2].lba_low = 128U;
    mock.commands[3] = command(7U, COSMOS_NVME_OPCODE_READ);
    mock.commands[3].data_address_low = 0U;
    mock.commands[3].data_address_high = 0U;
    mock.commands[4] = command(8U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[4].data_address_low = 0x00200002U;
    mock.commands[5] = command(9U, COSMOS_NVME_OPCODE_FLUSH);
    mock.commands[5].data_bytes = 512U;
    mock.command_count = 6U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.read_calls == 0U);
    CHECK(mock.program_calls == 0U);
    CHECK(mock.flush_calls == 0U);
    CHECK(mock.completion_count == 6U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_INVALID_OPCODE, 1U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_INVALID_NAMESPACE_FORMAT, 1U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_LBA_OUT_OF_RANGE, 1U));
    CHECK(completion_is(&mock.completions[3], &mock.commands[3],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(completion_is(&mock.completions[4], &mock.commands[4],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(completion_is(&mock.completions[5], &mock.commands[5],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_INVALID_FIELD, 1U));
    return 0;
}

static int test_data_address_bounds_are_exact_and_64_bit(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.commands[0] = command(10U, COSMOS_NVME_OPCODE_READ);
    mock.commands[0].data_address_low = 0xFFFFFE00U;
    mock.commands[0].data_address_high = 0xFFFFFFFFU;
    mock.commands[1] = command(11U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[1].data_bytes = 1024U;
    mock.commands[2] = command(12U, COSMOS_NVME_OPCODE_READ);
    mock.commands[2].data_address_low = 0x00204000U;
    mock.commands[2].data_address_high = 0x12345678U;
    mock.command_count = 3U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.program_calls == 0U);
    CHECK(mock.completion_count == 3U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_DATA_TRANSFER_ERROR, 1U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.last_data_address_low == 0x00204000U);
    CHECK(mock.last_data_address_high == 0x12345678U);
    return 0;
}

static int test_media_and_internal_failure_mapping(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.read_status = COSMOS_HW_ERROR;
    mock.program_status = COSMOS_TIMEOUT;
    mock.flush_status = COSMOS_HW_ERROR;
    mock.commands[0] = command(13U, COSMOS_NVME_OPCODE_READ);
    mock.commands[1] = command(14U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[2] = command(15U, COSMOS_NVME_OPCODE_FLUSH);
    mock.command_count = 3U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                        COSMOS_NVME_SC_UNRECOVERED_READ_ERROR, 0U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                        COSMOS_NVME_SC_WRITE_FAULT, 0U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                        COSMOS_NVME_SC_WRITE_FAULT, 0U));
    return 0;
}

static int test_retry_preserves_identity_without_reexecuting_media(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.post_results[0] = COSMOS_NVME_POST_NOT_COMMITTED_RETRY;
    mock.post_results[1] = COSMOS_NVME_POST_COMMITTED;
    mock.post_result_count = 2U;
    mock.commands[0] = command(30U, COSMOS_NVME_OPCODE_WRITE);
    mock.command_count = 1U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_RETRY);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.post_calls == 1U);
    CHECK(mock.completion_count == 0U);
    CHECK(service.completion_state == COSMOS_NVME_COMPLETION_RETRY);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.post_calls == 2U);
    CHECK(mock.completion_count == 1U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    return 0;
}

static int test_retry_does_not_consume_command_budget(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;
    unsigned int index;

    mock_reset(&mock);
    mock.post_results[0] = COSMOS_NVME_POST_NOT_COMMITTED_RETRY;
    mock.post_result_count = 1U;
    for (index = 0U; index < TEST_COMMAND_CAPACITY; index++) {
        mock.commands[index] = command(40U + index, COSMOS_NVME_OPCODE_FLUSH);
    }
    mock.command_count = TEST_COMMAND_CAPACITY;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_RETRY);
    CHECK(mock.fetch_index == 1U);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.fetch_index == COSMOS_NVME_SERVICE_BUDGET + 1U);
    CHECK(mock.completion_count == COSMOS_NVME_SERVICE_BUDGET + 1U);
    CHECK(mock.flush_calls == COSMOS_NVME_SERVICE_BUDGET + 1U);
    return 0;
}

static int test_ambiguous_post_is_latched_without_duplicate(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.post_results[0] = COSMOS_NVME_POST_AMBIGUOUS;
    mock.post_result_count = 1U;
    mock.commands[0] = command(60U, COSMOS_NVME_OPCODE_WRITE);
    mock.command_count = 1U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_COMPLETION_UNCERTAIN);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.post_calls == 1U);
    CHECK(mock.completion_count == 0U);
    CHECK(service.completion_state == COSMOS_NVME_COMPLETION_BLOCKED);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_COMPLETION_UNCERTAIN);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.post_calls == 1U);
    CHECK(mock.completion_count == 0U);
    return 0;
}

static int test_hard_post_failure_is_latched_without_duplicate(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.post_results[0] = COSMOS_NVME_POST_HARD_FAILED;
    mock.post_result_count = 1U;
    mock.commands[0] = command(61U, COSMOS_NVME_OPCODE_READ);
    mock.command_count = 1U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_HW_ERROR);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.post_calls == 1U);
    CHECK(mock.completion_count == 0U);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_HW_ERROR);
    CHECK(mock.fetch_index == 1U);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.post_calls == 1U);
    CHECK(mock.completion_count == 0U);
    return 0;
}

static int test_write_zeroes_and_deallocate(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.commands[0] = command(70U, COSMOS_NVME_OPCODE_WRITE_ZEROES);
    mock.commands[0].lba_low = 4U;
    mock.commands[0].nlb = 3U;
    mock.commands[0].control = COSMOS_NVME_WRITE_ZEROES_LR |
        COSMOS_NVME_WRITE_ZEROES_FUA | COSMOS_NVME_WRITE_ZEROES_DEAC;
    mock.commands[1] = command(
        71U, COSMOS_NVME_OPCODE_DATASET_MANAGEMENT);
    mock.commands[1].dataset_attributes = COSMOS_NVME_DSM_ATTRIBUTE_MASK;
    mock.commands[1].dataset_range_count = 2U;
    mock.commands[1].data_address_low = 0x00200000U;
    mock.commands[1].data_address_high = 1U;
    mock.commands[1].data_bytes = 2U * COSMOS_NVME_DSM_RANGE_BYTES;
    mock.commands[2] = command(72U, COSMOS_NVME_OPCODE_WRITE_ZEROES);
    mock.commands[2].control = 1U;
    mock.commands[3] = command(
        73U, COSMOS_NVME_OPCODE_DATASET_MANAGEMENT);
    mock.commands[3].dataset_range_count = 1U;
    mock.commands[3].data_address_low = 0x00200000U;
    mock.commands[3].data_bytes = COSMOS_NVME_DSM_RANGE_BYTES;
    mock.commands[4] = command(74U, COSMOS_NVME_OPCODE_WRITE_ZEROES);
    mock.commands[4].lba_low = 128U;
    mock.commands[5] = command(
        77U, COSMOS_NVME_OPCODE_DATASET_MANAGEMENT);
    mock.commands[5].dataset_attributes = 1U;
    mock.commands[5].dataset_range_count = 1U;
    mock.commands[5].data_address_low = 0x00200000U;
    mock.commands[5].data_bytes = COSMOS_NVME_DSM_RANGE_BYTES;
    mock.command_count = 6U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.zeroes_calls == 1U);
    CHECK(mock.deallocate_calls == 1U);
    CHECK(mock.flush_calls == 1U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_GENERIC, COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_INVALID_FIELD, 1U));
    CHECK(completion_is(&mock.completions[3], &mock.commands[3],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[4], &mock.commands[4],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_LBA_OUT_OF_RANGE, 1U));
    CHECK(completion_is(&mock.completions[5], &mock.commands[5],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(mock.deallocate_calls == 1U);
    return 0;
}

static int test_zeroes_and_deallocate_failure_mapping(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.program_status = COSMOS_HW_ERROR;
    mock.commands[0] = command(75U, COSMOS_NVME_OPCODE_WRITE_ZEROES);
    mock.commands[1] = command(
        76U, COSMOS_NVME_OPCODE_DATASET_MANAGEMENT);
    mock.commands[1].dataset_attributes =
        COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE;
    mock.commands[1].dataset_range_count = 1U;
    mock.commands[1].data_address_low = 0x00200000U;
    mock.commands[1].data_bytes = COSMOS_NVME_DSM_RANGE_BYTES;
    mock.command_count = 2U;
    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                        COSMOS_NVME_SC_WRITE_FAULT, 0U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_MEDIA_DATA_INTEGRITY,
                        COSMOS_NVME_SC_WRITE_FAULT, 0U));
    return 0;
}

static int test_rw_fua_and_limited_retry_contract(void) {
    struct mock_adapter mock;
    struct cosmos_nvme_service service;

    mock_reset(&mock);
    mock.commands[0] = command(80U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[0].control = COSMOS_NVME_RW_FUA | COSMOS_NVME_RW_LR;
    mock.commands[1] = command(81U, COSMOS_NVME_OPCODE_READ);
    mock.commands[1].control = COSMOS_NVME_RW_LR;
    mock.commands[2] = command(82U, COSMOS_NVME_OPCODE_WRITE);
    mock.commands[2].control = 1U << 29U;
    mock.command_count = 3U;

    CHECK(service_init(&service, &mock) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(mock.program_calls == 1U);
    CHECK(mock.read_calls == 1U);
    CHECK(mock.flush_calls == 1U);
    CHECK(completion_is(&mock.completions[0], &mock.commands[0],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[1], &mock.commands[1],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_SUCCESS, 0U));
    CHECK(completion_is(&mock.completions[2], &mock.commands[2],
                        COSMOS_NVME_SCT_GENERIC,
                        COSMOS_NVME_SC_INVALID_FIELD, 1U));
    return 0;
}

int main(void) {
#ifdef COSMOS_NVME_FUA_ONLY
    CHECK(test_rw_fua_and_limited_retry_contract() == 0);
    puts("cosmos NVMe FUA/LR contract: PASS");
#else
    CHECK(test_empty_queue() == 0);
    CHECK(test_success_paths_preserve_identity_and_address() == 0);
    CHECK(test_status_mapping_and_no_media() == 0);
    CHECK(test_data_address_bounds_are_exact_and_64_bit() == 0);
    CHECK(test_media_and_internal_failure_mapping() == 0);
    CHECK(test_retry_preserves_identity_without_reexecuting_media() == 0);
    CHECK(test_retry_does_not_consume_command_budget() == 0);
    CHECK(test_ambiguous_post_is_latched_without_duplicate() == 0);
    CHECK(test_hard_post_failure_is_latched_without_duplicate() == 0);
    CHECK(test_write_zeroes_and_deallocate() == 0);
    CHECK(test_zeroes_and_deallocate_failure_mapping() == 0);
    puts("cosmos NVMe firmware contract: PASS");
#endif
    return 0;
}
