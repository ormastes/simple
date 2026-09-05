#include <stdio.h>
#include <string.h>

#include "cosmos_nvme_dispatch.h"
#include "cosmos_pcie_regs.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_CAPACITY 8U

struct transport_mock {
    struct cosmos_pcie_nvme_command commands[TEST_CAPACITY];
    enum cosmos_pcie_nvme_completion_result results[TEST_CAPACITY];
    unsigned int command_count;
    unsigned int command_index;
    unsigned int result_count;
    unsigned int result_index;
    unsigned int fetch_calls;
    unsigned int post_calls;
    unsigned int last_queue_id;
    unsigned int last_specific;
    unsigned int last_sc;
};

struct fixture {
    struct cosmos_nvme_service io;
    struct cosmos_nvme_admin_service admin;
    struct cosmos_nvme_pcie_bridge bridge;
    struct cosmos_nvme_dispatch dispatch;
    unsigned int read_calls;
    unsigned int flush_calls;
    unsigned int payload_calls;
};

static struct transport_mock transport;

static void reset_transport(void) {
    memset(&transport, 0, sizeof(transport));
}

int cosmos_pcie_nvme_fetch_command(struct cosmos_pcie_nvme_command *command) {
    transport.fetch_calls++;
    if (command == 0) {
        return COSMOS_INVALID;
    }
    if (transport.command_index == transport.command_count) {
        return COSMOS_UNAVAILABLE;
    }
    *command = transport.commands[transport.command_index++];
    return COSMOS_OK;
}

enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion(
    const struct cosmos_pcie_nvme_completion *completion) {
    (void)completion;
    return COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
}

enum cosmos_pcie_nvme_completion_result cosmos_pcie_nvme_post_completion_fields(
    unsigned int queue_id, unsigned int slot_tag, unsigned int sequence,
    unsigned int cid, unsigned int specific, unsigned int sct,
    unsigned int sc, unsigned int dnr) {
    enum cosmos_pcie_nvme_completion_result result =
        COSMOS_PCIE_NVME_COMPLETION_COMMITTED;

    (void)slot_tag;
    (void)sequence;
    (void)cid;
    (void)sct;
    (void)dnr;
    transport.post_calls++;
    transport.last_queue_id = queue_id;
    transport.last_specific = specific;
    transport.last_sc = sc;
    if (transport.result_index < transport.result_count) {
        result = transport.results[transport.result_index++];
    }
    return result;
}

int cosmos_pcie_nvme_configure_io_sq(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    (void)queue_id;
    (void)valid;
    (void)completion_queue_id;
    (void)entries;
    (void)address_low;
    (void)address_high;
    return COSMOS_OK;
}

int cosmos_pcie_nvme_configure_io_cq(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    (void)queue_id;
    (void)valid;
    (void)irq_enable;
    (void)irq_vector;
    (void)entries;
    (void)address_low;
    (void)address_high;
    return COSMOS_OK;
}

int cosmos_pcie_host_dma_submit_device_to_host(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length) {
    (void)device_address;
    (void)host_address_high;
    (void)host_address_low;
    (void)length;
    return COSMOS_OK;
}

int cosmos_pcie_host_dma_poll_direct(
    enum cosmos_pcie_host_dma_direction direction) {
    (void)direction;
    return COSMOS_OK;
}

static int media_read(
    void *context, const struct cosmos_nvme_command *command) {
    struct fixture *fixture = context;

    (void)command;
    fixture->read_calls++;
    return COSMOS_OK;
}

static int media_program(
    void *context, const struct cosmos_nvme_command *command) {
    (void)context;
    (void)command;
    return COSMOS_OK;
}

static int media_flush(void *context) {
    struct fixture *fixture = context;

    fixture->flush_calls++;
    return COSMOS_OK;
}

static int media_zeroes(
    void *context, const struct cosmos_nvme_command *command) {
    (void)context;
    (void)command;
    return COSMOS_OK;
}

static int media_deallocate(
    void *context, const struct cosmos_nvme_command *command) {
    (void)context;
    (void)command;
    return COSMOS_OK;
}

static enum cosmos_nvme_admin_payload_result write_payload(
    void *context, const struct cosmos_nvme_admin_command *command,
    const unsigned char *payload, unsigned int payload_bytes) {
    struct fixture *fixture = context;

    (void)command;
    (void)payload;
    (void)payload_bytes;
    fixture->payload_calls++;
    return COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED;
}

static int fixture_init(struct fixture *fixture) {
    struct cosmos_nvme_admin_adapter admin_adapter;
    int status;

    memset(fixture, 0, sizeof(*fixture));
    status = cosmos_nvme_pcie_service_init(
        &fixture->io, &fixture->bridge, fixture, media_read, media_program,
        media_flush, media_zeroes, media_deallocate, 1024U, 0U, 512U);
    if (status != COSMOS_OK) {
        return status;
    }
    memset(&admin_adapter, 0, sizeof(admin_adapter));
    admin_adapter.context = fixture;
    admin_adapter.post_completion = cosmos_nvme_pcie_post_admin_completion;
    admin_adapter.write_payload = write_payload;
    admin_adapter.configure_io_sq = cosmos_nvme_pcie_configure_io_sq;
    admin_adapter.configure_io_cq = cosmos_nvme_pcie_configure_io_cq;
    status = cosmos_nvme_admin_init(&fixture->admin, &admin_adapter, 1024U,
                                    0U, 512U);
    if (status != COSMOS_OK) {
        return status;
    }
    fixture->admin.completion_queues[0].valid = 1U;
    fixture->admin.submission_queues[0].valid = 1U;
    fixture->admin.submission_queues[0].completion_queue_id = 1U;
    return cosmos_nvme_dispatch_init(&fixture->dispatch, &fixture->bridge,
                                     &fixture->io, &fixture->admin);
}

static struct cosmos_pcie_nvme_command command_make(
    unsigned int queue_id, unsigned int opcode, unsigned int cid) {
    struct cosmos_pcie_nvme_command command;

    memset(&command, 0, sizeof(command));
    command.queue_id = queue_id;
    command.slot_tag = cid + 1U;
    command.sequence = cid + 2U;
    command.raw_dword[0] = (cid << 16U) | opcode;
    return command;
}

static int test_routes_one_raw_command(void) {
    struct fixture fixture;

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    transport.commands[0] = command_make(
        0U, COSMOS_NVME_ADMIN_GET_FEATURES, 1U);
    transport.commands[0].raw_dword[10] =
        COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    transport.commands[1] = command_make(
        1U, COSMOS_NVME_OPCODE_READ, 2U);
    transport.commands[1].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.commands[1].raw_dword[6] = 0x00200000U;
    transport.command_count = 2U;

    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_OK);
    CHECK(transport.fetch_calls == 1U);
    CHECK(transport.post_calls == 1U);
    CHECK(transport.last_queue_id == 0U);
    CHECK(transport.last_specific == 0x00030003U);
    CHECK(fixture.read_calls == 0U);

    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_OK);
    CHECK(transport.fetch_calls == 2U);
    CHECK(transport.post_calls == 2U);
    CHECK(transport.last_queue_id == 1U);
    CHECK(fixture.read_calls == 1U);
    return 0;
}

static int test_reserved_fields_fail_closed(void) {
    struct fixture fixture;

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    transport.commands[0] = command_make(
        0U, COSMOS_NVME_ADMIN_GET_FEATURES, 3U);
    transport.commands[0].raw_dword[2] = 1U;
    transport.commands[0].raw_dword[10] =
        COSMOS_NVME_ADMIN_FEATURE_NUMBER_OF_QUEUES;
    transport.commands[1] = command_make(
        1U, COSMOS_NVME_OPCODE_READ, 4U);
    transport.commands[1].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.commands[1].raw_dword[6] = 0x00200000U;
    transport.commands[1].raw_dword[2] = 1U;
    transport.command_count = 2U;

    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_OK);
    CHECK(transport.last_sc == COSMOS_NVME_SC_INVALID_FIELD);
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_OK);
    CHECK(transport.last_sc == COSMOS_NVME_SC_INVALID_FIELD);
    CHECK(fixture.read_calls == 0U);
    return 0;
}

static int test_retry_blocks_fetch(void) {
    struct fixture fixture;

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    transport.commands[0] = command_make(
        1U, COSMOS_NVME_OPCODE_FLUSH, 5U);
    transport.commands[0].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.command_count = 1U;
    transport.results[0] = COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
    transport.results[1] = COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
    transport.results[2] = COSMOS_PCIE_NVME_COMPLETION_COMMITTED;
    transport.result_count = 3U;

    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_RETRY);
    CHECK(transport.fetch_calls == 1U);
    CHECK(fixture.flush_calls == 1U);
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_RETRY);
    CHECK(transport.fetch_calls == 1U);
    CHECK(fixture.flush_calls == 1U);
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_OK);
    CHECK(transport.fetch_calls == 2U);
    CHECK(fixture.flush_calls == 1U);
    return 0;
}

static int test_terminal_completion_blocks_fetch(void) {
    struct fixture fixture;

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    transport.commands[0] = command_make(
        1U, COSMOS_NVME_OPCODE_FLUSH, 6U);
    transport.commands[0].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.command_count = 1U;
    transport.results[0] = COSMOS_PCIE_NVME_COMPLETION_AMBIGUOUS;
    transport.result_count = 1U;

    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) ==
          COSMOS_COMPLETION_UNCERTAIN);
    CHECK(transport.fetch_calls == 1U);
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) ==
          COSMOS_COMPLETION_UNCERTAIN);
    CHECK(transport.fetch_calls == 1U);
    return 0;
}

static int test_unconfigured_queue_faults_without_media(void) {
    struct fixture fixture;

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    transport.commands[0] = command_make(
        5U, COSMOS_NVME_OPCODE_READ, 7U);
    transport.commands[0].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.commands[0].raw_dword[6] = 0x00200000U;
    transport.command_count = 1U;
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_HW_ERROR);
    CHECK(transport.fetch_calls == 1U);
    CHECK(fixture.read_calls == 0U);
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_HW_ERROR);
    CHECK(transport.fetch_calls == 1U);

    reset_transport();
    CHECK(fixture_init(&fixture) == COSMOS_OK);
    fixture.admin.submission_queues[0].valid = 0U;
    transport.commands[0] = command_make(
        1U, COSMOS_NVME_OPCODE_READ, 8U);
    transport.commands[0].raw_dword[1] = COSMOS_NVME_NAMESPACE_ID;
    transport.commands[0].raw_dword[6] = 0x00200000U;
    transport.command_count = 1U;
    CHECK(cosmos_nvme_dispatch_poll(&fixture.dispatch) == COSMOS_HW_ERROR);
    CHECK(fixture.read_calls == 0U);
    return 0;
}

int main(void) {
#ifdef COSMOS_NVME_DISPATCH_QUEUE_ONLY
    CHECK(test_unconfigured_queue_faults_without_media() == 0);
    puts("cosmos NVMe dispatcher queue admission: PASS");
#else
    CHECK(test_routes_one_raw_command() == 0);
    CHECK(test_reserved_fields_fail_closed() == 0);
    CHECK(test_retry_blocks_fetch() == 0);
    CHECK(test_terminal_completion_blocks_fetch() == 0);
    puts("cosmos NVMe dispatcher contract: PASS");
#endif
    return 0;
}
