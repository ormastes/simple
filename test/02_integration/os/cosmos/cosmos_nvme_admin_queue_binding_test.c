#include <stdio.h>
#include <string.h>

#include "cosmos_nvme_admin.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

struct queue_mock {
    struct cosmos_nvme_admin_completion completion;
    unsigned int sq_calls;
    unsigned int cq_calls;
    unsigned int last_valid;
    unsigned int fail_config;
};

static enum cosmos_nvme_post_result post(
    void *context, const struct cosmos_nvme_admin_completion *completion) {
    struct queue_mock *mock = context;

    mock->completion = *completion;
    return COSMOS_NVME_POST_COMMITTED;
}

static enum cosmos_nvme_admin_payload_result payload(
    void *context, const struct cosmos_nvme_admin_command *command,
    const unsigned char *bytes, unsigned int count) {
    (void)context;
    (void)command;
    (void)bytes;
    (void)count;
    return COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED;
}

static int configure_sq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    struct queue_mock *mock = context;

    (void)queue_id;
    (void)completion_queue_id;
    (void)entries;
    (void)address_low;
    (void)address_high;
    mock->sq_calls++;
    mock->last_valid = valid;
    return mock->fail_config != 0U ? COSMOS_HW_ERROR : COSMOS_OK;
}

static int configure_cq(
    void *context, unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    struct queue_mock *mock = context;

    (void)queue_id;
    (void)irq_enable;
    (void)irq_vector;
    (void)entries;
    (void)address_low;
    (void)address_high;
    mock->cq_calls++;
    mock->last_valid = valid;
    return mock->fail_config != 0U ? COSMOS_HW_ERROR : COSMOS_OK;
}

static struct cosmos_nvme_admin_command command(
    unsigned int cid, unsigned int opcode) {
    struct cosmos_nvme_admin_command value;

    memset(&value, 0, sizeof(value));
    value.cid = cid;
    value.slot_tag = cid;
    value.sequence = cid;
    value.opcode = opcode;
    return value;
}

static int accept(
    struct cosmos_nvme_admin_service *service,
    struct cosmos_nvme_admin_command *command) {
    return cosmos_nvme_admin_accept(service, command);
}

int main(void) {
    struct cosmos_nvme_admin_service service;
    struct cosmos_nvme_admin_adapter adapter;
    struct cosmos_nvme_admin_command cmd;
    struct queue_mock mock;

    memset(&mock, 0, sizeof(mock));
    memset(&adapter, 0, sizeof(adapter));
    adapter.context = &mock;
    adapter.post_completion = post;
    adapter.write_payload = payload;
    adapter.configure_io_sq = configure_sq;
    adapter.configure_io_cq = configure_cq;
    CHECK(cosmos_nvme_admin_init(
              &service, &adapter, 1024U, 0U, 512U) == COSMOS_OK);

    cmd = command(1U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    cmd.cdw10 = 1U | (3U << 16U);
    cmd.cdw11 = 3U;
    cmd.payload_address_low = 0x00400000U;
    CHECK(accept(&service, &cmd) == COSMOS_OK);
    CHECK(mock.cq_calls == 1U && mock.last_valid == 1U);
    CHECK(service.completion_queues[0].valid == 1U);

    cmd = command(2U, COSMOS_NVME_ADMIN_CREATE_IO_SQ);
    cmd.cdw10 = 1U | (3U << 16U);
    cmd.cdw11 = 1U | (1U << 16U);
    cmd.payload_address_low = 0x00500000U;
    CHECK(accept(&service, &cmd) == COSMOS_OK);
    CHECK(mock.sq_calls == 1U && mock.last_valid == 1U);
    CHECK(service.submission_queues[0].valid == 1U);

    cmd = command(3U, COSMOS_NVME_ADMIN_DELETE_IO_SQ);
    cmd.cdw10 = 1U;
    CHECK(accept(&service, &cmd) == COSMOS_OK);
    CHECK(mock.sq_calls == 2U && mock.last_valid == 0U);
    CHECK(service.submission_queues[0].valid == 0U);

    cmd = command(4U, COSMOS_NVME_ADMIN_DELETE_IO_CQ);
    cmd.cdw10 = 1U;
    CHECK(accept(&service, &cmd) == COSMOS_OK);
    CHECK(mock.cq_calls == 2U && mock.last_valid == 0U);
    CHECK(service.completion_queues[0].valid == 0U);

    mock.fail_config = 1U;
    cmd = command(5U, COSMOS_NVME_ADMIN_CREATE_IO_CQ);
    cmd.cdw10 = 1U | (3U << 16U);
    cmd.cdw11 = 1U;
    cmd.payload_address_low = 0x00600000U;
    CHECK(accept(&service, &cmd) == COSMOS_OK);
    CHECK(mock.completion.status.sc == COSMOS_NVME_SC_INTERNAL_DEVICE_ERROR);
    CHECK(service.completion_queues[0].valid == 0U);
    puts("cosmos NVMe admin queue binding: PASS");
    return 0;
}
