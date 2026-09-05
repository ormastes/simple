#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>

#include "cosmos_nvme_pcie_adapter.h"
#include "cosmos_nfc_regs.h"
#include "cosmos_pcie_regs.h"

#define CHECK(condition)                                                      \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_COMMAND_CAPACITY (COSMOS_NVME_SERVICE_BUDGET + 3U)
#define TEST_BLOCK_BYTES 512U

struct pcie_mock {
    struct cosmos_pcie_nvme_command commands[TEST_COMMAND_CAPACITY];
    enum cosmos_pcie_nvme_completion_result post_results[TEST_COMMAND_CAPACITY];
    unsigned int command_count;
    unsigned int fetch_index;
    unsigned int fetch_calls;
    unsigned int post_calls;
    unsigned int committed_count;
    unsigned int post_result_count;
    unsigned int post_result_index;
    unsigned int posted_queue_id[TEST_COMMAND_CAPACITY];
    unsigned int posted_slot_tag[TEST_COMMAND_CAPACITY];
    unsigned int posted_sequence[TEST_COMMAND_CAPACITY];
    unsigned int posted_cid[TEST_COMMAND_CAPACITY];
    unsigned int posted_sct[TEST_COMMAND_CAPACITY];
    unsigned int posted_sc[TEST_COMMAND_CAPACITY];
    unsigned int posted_dnr[TEST_COMMAND_CAPACITY];
    unsigned int last_queue_id;
    unsigned int last_slot_tag;
    unsigned int last_sequence;
    unsigned int last_cid;
    unsigned int last_specific;
    unsigned int last_sct;
    unsigned int last_sc;
    unsigned int last_dnr;
};

struct media_mock {
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
};

static struct pcie_mock g_pcie;
static int g_dma_submit_results[4];
static int g_dma_poll_results[4];
static unsigned int g_dma_submit_count;
static unsigned int g_dma_poll_count;
static int g_admin_init_result;

#ifdef COSMOS_NVME_PCIE_ADAPTER_COVERAGE_ONLY
int cosmos_nvme_service_init(struct cosmos_nvme_service *service,
                             const struct cosmos_nvme_adapter *adapter,
                             unsigned int namespace_blocks_low,
                             unsigned int namespace_blocks_high,
                             unsigned int block_bytes) {
    service->adapter = *adapter;
    service->namespace_blocks_low = namespace_blocks_low;
    service->namespace_blocks_high = namespace_blocks_high;
    service->block_bytes = block_bytes;
    return COSMOS_OK;
}
#endif

static void reset_pcie(void) {
    memset(&g_pcie, 0, sizeof(g_pcie));
}

static void reset_dma(void) {
    unsigned int index;

    for (index = 0U; index < 4U; ++index) {
        g_dma_submit_results[index] = COSMOS_INVALID;
        g_dma_poll_results[index] = COSMOS_INVALID;
    }
    g_dma_submit_count = 0U;
    g_dma_poll_count = 0U;
}

static void reset_media(struct media_mock *media) {
    memset(media, 0, sizeof(*media));
}

static struct cosmos_pcie_nvme_command make_raw_command(
    unsigned int queue_id, unsigned int slot_tag, unsigned int sequence,
    unsigned int opcode, unsigned int cid, unsigned int namespace_id,
    unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_low, unsigned int prp2_high,
    unsigned int slba_low, unsigned int slba_high, unsigned int nlb) {
    struct cosmos_pcie_nvme_command command;

    memset(&command, 0, sizeof(command));
    command.queue_id = queue_id;
    command.slot_tag = slot_tag;
    command.sequence = sequence;
    command.raw_dword[0] = (cid << 16U) | opcode;
    command.raw_dword[1] = namespace_id;
    command.raw_dword[6] = prp1_low;
    command.raw_dword[7] = prp1_high;
    command.raw_dword[8] = prp2_low;
    command.raw_dword[9] = prp2_high;
    command.raw_dword[10] = slba_low;
    command.raw_dword[11] = slba_high;
    command.raw_dword[12] = nlb;
    return command;
}

int cosmos_pcie_nvme_fetch_command(struct cosmos_pcie_nvme_command *command) {
    g_pcie.fetch_calls++;
    if (command == 0) {
        return COSMOS_INVALID;
    }
    if (g_pcie.fetch_index == g_pcie.command_count) {
        return COSMOS_UNAVAILABLE;
    }
    *command = g_pcie.commands[g_pcie.fetch_index++];
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

    g_pcie.post_calls++;
    g_pcie.last_queue_id = queue_id;
    g_pcie.last_slot_tag = slot_tag;
    g_pcie.last_sequence = sequence;
    g_pcie.last_cid = cid;
    g_pcie.last_specific = specific;
    g_pcie.last_sct = sct;
    g_pcie.last_sc = sc;
    g_pcie.last_dnr = dnr;
    if (g_pcie.post_calls <= TEST_COMMAND_CAPACITY) {
        unsigned int index = g_pcie.post_calls - 1U;

        g_pcie.posted_queue_id[index] = queue_id;
        g_pcie.posted_slot_tag[index] = slot_tag;
        g_pcie.posted_sequence[index] = sequence;
        g_pcie.posted_cid[index] = cid;
        g_pcie.posted_sct[index] = sct;
        g_pcie.posted_sc[index] = sc;
        g_pcie.posted_dnr[index] = dnr;
    }
    if (g_pcie.post_result_index < g_pcie.post_result_count) {
        result = g_pcie.post_results[g_pcie.post_result_index++];
    }
    if (result == COSMOS_PCIE_NVME_COMPLETION_COMMITTED) {
        g_pcie.committed_count++;
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
    if (g_dma_submit_count < 4U) {
        return g_dma_submit_results[g_dma_submit_count++];
    }
    return COSMOS_INVALID;
}

int cosmos_pcie_host_dma_poll_direct(
    enum cosmos_pcie_host_dma_direction direction) {
    (void)direction;
    if (g_dma_poll_count < 4U) {
        return g_dma_poll_results[g_dma_poll_count++];
    }
    return COSMOS_INVALID;
}

int cosmos_nvme_admin_init(struct cosmos_nvme_admin_service *service,
                           const struct cosmos_nvme_admin_adapter *adapter,
                           unsigned int namespace_blocks_low,
                           unsigned int namespace_blocks_high,
                           unsigned int block_bytes) {
    if (g_admin_init_result != COSMOS_OK) {
        return g_admin_init_result;
    }
    service->adapter = *adapter;
    service->namespace_blocks_low = namespace_blocks_low;
    service->namespace_blocks_high = namespace_blocks_high;
    service->block_bytes = block_bytes;
    return COSMOS_OK;
}

static int media_read(
    void *context, const struct cosmos_nvme_command *command) {
    struct media_mock *media = context;

    media->read_calls++;
    media->last_lba_low = command->lba_low;
    media->last_lba_high = command->lba_high;
    media->last_block_count = command->nlb + 1U;
    media->last_data_address_low = command->data_address_low;
    media->last_data_address_high = command->data_address_high;
    media->last_data_bytes = command->data_bytes;
    return COSMOS_OK;
}

static int media_program(
    void *context, const struct cosmos_nvme_command *command) {
    struct media_mock *media = context;

    media->program_calls++;
    media->last_lba_low = command->lba_low;
    media->last_lba_high = command->lba_high;
    media->last_block_count = command->nlb + 1U;
    media->last_data_address_low = command->data_address_low;
    media->last_data_address_high = command->data_address_high;
    media->last_data_bytes = command->data_bytes;
    return COSMOS_OK;
}

static int media_flush(void *context) {
    struct media_mock *media = context;

    media->flush_calls++;
    return COSMOS_OK;
}

static int media_write_zeroes(
    void *context, const struct cosmos_nvme_command *command) {
    struct media_mock *media = context;

    media->zeroes_calls++;
    media->last_lba_low = command->lba_low;
    media->last_lba_high = command->lba_high;
    media->last_block_count = command->nlb + 1U;
    return COSMOS_OK;
}

static int media_deallocate(
    void *context, const struct cosmos_nvme_command *command) {
    struct media_mock *media = context;

    media->deallocate_calls++;
    media->last_data_address_low = command->data_address_low;
    media->last_data_address_high = command->data_address_high;
    media->last_block_count = command->dataset_range_count;
    media->last_data_bytes = command->data_bytes;
    return COSMOS_OK;
}

static int bridge_init(struct cosmos_nvme_service *service,
                       struct cosmos_nvme_pcie_bridge *bridge,
                       struct media_mock *media) {
    return cosmos_nvme_pcie_service_init(
        service, bridge, media, media_read, media_program, media_flush,
        media_write_zeroes, media_deallocate, 0U, 0x11223345U,
        TEST_BLOCK_BYTES);
}

static int test_exact_decode_and_forwarding(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_pcie();
    reset_media(&media);
    g_pcie.commands[0] = make_raw_command(
        7U, 0x34U, 0x56U, COSMOS_NVME_OPCODE_READ, 0xCAFEU,
        COSMOS_NVME_NAMESPACE_ID, 0x00200F00U, 1U,
        0x00201000U, 1U, 0x55667788U, 0x11223344U, 1U);
    g_pcie.command_count = 1U;

    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(media.read_calls == 1U);
    CHECK(media.program_calls == 0U);
    CHECK(media.last_lba_low == 0x55667788U);
    CHECK(media.last_lba_high == 0x11223344U);
    CHECK(media.last_block_count == 2U);
    CHECK(media.last_data_address_low == 0x00200F00U);
    CHECK(media.last_data_address_high == 1U);
    CHECK(media.last_data_bytes == 1024U);
    CHECK(g_pcie.last_queue_id == 7U);
    CHECK(g_pcie.last_slot_tag == 0x34U);
    CHECK(g_pcie.last_sequence == 0x56U);
    CHECK(g_pcie.last_cid == 0xCAFEU);
    CHECK(g_pcie.last_specific == 0U);
    CHECK(g_pcie.last_sct == COSMOS_NVME_SCT_GENERIC);
    CHECK(g_pcie.last_sc == COSMOS_NVME_SC_SUCCESS);
    CHECK(g_pcie.last_dnr == 0U);
    return 0;
}

static int test_prp2_and_sgl_validation(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_pcie();
    reset_media(&media);
    g_pcie.commands[0] = make_raw_command(
        1U, 2U, 3U, COSMOS_NVME_OPCODE_WRITE, 0x1001U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200F00U, 0U, 0x00202000U, 0U,
        4U, 0U, 1U);
    g_pcie.commands[1] = make_raw_command(
        4U, 5U, 6U, COSMOS_NVME_OPCODE_READ, 0x1002U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200000U, 0U, 0U, 0U,
        8U, 0U, 0U);
    g_pcie.commands[1].raw_dword[0] |= 1U << 14U;
    g_pcie.commands[2] = make_raw_command(
        5U, 6U, 7U, COSMOS_NVME_OPCODE_READ, 0x1003U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200000U, 0U, 0x00201000U, 0U,
        12U, 0U, 0U);
    g_pcie.commands[3] = make_raw_command(
        6U, 7U, 8U, COSMOS_NVME_OPCODE_READ, 0x1004U,
        COSMOS_NVME_NAMESPACE_ID, 0xFFFFFF00U, 0xFFFFFFFFU, 0U, 0U,
        16U, 0U, 0U);
    g_pcie.command_count = 4U;

    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(media.read_calls == 0U);
    CHECK(media.program_calls == 1U);
    CHECK(g_pcie.post_calls == 4U);
    CHECK(g_pcie.posted_queue_id[0] == 1U);
    CHECK(g_pcie.posted_slot_tag[0] == 2U);
    CHECK(g_pcie.posted_sequence[0] == 3U);
    CHECK(g_pcie.posted_cid[0] == 0x1001U);
    CHECK(g_pcie.posted_sct[0] == COSMOS_NVME_SCT_GENERIC);
    CHECK(g_pcie.posted_sc[0] == COSMOS_NVME_SC_SUCCESS);
    CHECK(g_pcie.posted_dnr[0] == 0U);
    CHECK(g_pcie.posted_queue_id[1] == 4U);
    CHECK(g_pcie.posted_slot_tag[1] == 5U);
    CHECK(g_pcie.posted_sequence[1] == 6U);
    CHECK(g_pcie.posted_cid[1] == 0x1002U);
    CHECK(g_pcie.posted_sct[1] == COSMOS_NVME_SCT_GENERIC);
    CHECK(g_pcie.posted_sc[1] == COSMOS_NVME_SC_INVALID_FIELD);
    CHECK(g_pcie.posted_dnr[1] == 1U);
    CHECK(g_pcie.posted_queue_id[2] == 5U);
    CHECK(g_pcie.posted_cid[2] == 0x1003U);
    CHECK(g_pcie.posted_sct[2] == COSMOS_NVME_SCT_GENERIC);
    CHECK(g_pcie.posted_sc[2] == COSMOS_NVME_SC_INVALID_FIELD);
    CHECK(g_pcie.posted_dnr[2] == 1U);
    CHECK(g_pcie.posted_queue_id[3] == 6U);
    CHECK(g_pcie.posted_cid[3] == 0x1004U);
    CHECK(g_pcie.posted_sct[3] == COSMOS_NVME_SCT_GENERIC);
    CHECK(g_pcie.posted_sc[3] == COSMOS_NVME_SC_INVALID_FIELD);
    CHECK(g_pcie.posted_dnr[3] == 1U);
    return 0;
}

static int test_init_rejects_missing_media(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_media(&media);
    CHECK(cosmos_nvme_pcie_service_init(
              0, &bridge, &media, media_read, media_program, media_flush,
              media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, 0, &media, media_read, media_program, media_flush,
              media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, 0, media_program, media_flush,
              media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, 0, media_flush,
              media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, 0, media_read, media_program, media_flush,
              media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              0, media_write_zeroes, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              media_flush, media_write_zeroes, media_deallocate, 0U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              media_flush, media_write_zeroes, media_deallocate, 1U, 0U,
              3U) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              media_flush, media_write_zeroes, media_deallocate, 1U, 0U,
              768U) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              media_flush, 0, media_deallocate, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_service_init(
              &service, &bridge, &media, media_read, media_program,
              media_flush, media_write_zeroes, 0, 1U, 0U,
              TEST_BLOCK_BYTES) == COSMOS_INVALID);
    return 0;
}

static int test_pointer_and_scalar_marshalling_edges(void) {
    struct cosmos_nvme_pcie_bridge bridge;
    struct cosmos_pcie_nvme_command raw;
    struct cosmos_nvme_command command;
    struct cosmos_nvme_admin_command admin;

    memset(&bridge, 0, sizeof(bridge));
    bridge.block_bytes = TEST_BLOCK_BYTES;
    raw = make_raw_command(1U, 2U, 3U, 0xFFU, 4U, 0U,
                           0U, 0U, 0U, 0U, 0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_io(0, &raw, &command) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, 0, &command) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, 0) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    CHECK(command.opcode == 0xFFU);

    raw = make_raw_command(1U, 2U, 3U, COSMOS_NVME_OPCODE_FLUSH, 4U,
                           COSMOS_NVME_NAMESPACE_ID, 0U, 0U, 0U, 0U,
                           0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    raw = make_raw_command(1U, 2U, 3U, COSMOS_NVME_OPCODE_WRITE_ZEROES, 4U,
                           COSMOS_NVME_NAMESPACE_ID, 0U, 0U, 0U, 0U,
                           0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    raw = make_raw_command(1U, 2U, 3U,
                           COSMOS_NVME_OPCODE_DATASET_MANAGEMENT, 4U,
                           COSMOS_NVME_NAMESPACE_ID, 0x00200000U, 0U,
                           0U, 0U, 0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    raw = make_raw_command(1U, 2U, 3U, COSMOS_NVME_OPCODE_READ, 4U,
                           COSMOS_NVME_NAMESPACE_ID, 0x00200000U, 0U,
                           0U, 0U, 0U, 0U, 0U);
    raw.raw_dword[2] = 1U;
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    CHECK(command.opcode == COSMOS_NVME_OPCODE_FLUSH);

    CHECK(cosmos_nvme_pcie_decode_admin(0, &admin) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_decode_admin(&raw, 0) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_decode_admin(&raw, &admin) == COSMOS_OK);
    CHECK(admin.payload_bytes == 0U);

    raw = make_raw_command(0U, 2U, 3U, COSMOS_NVME_ADMIN_CREATE_IO_SQ,
                           5U, 0U, 0x00200000U, 1U, 0U, 0U,
                           0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_admin(&raw, &admin) == COSMOS_OK);
    CHECK(admin.payload_address_low == 0x00200000U);

    raw = make_raw_command(0U, 2U, 3U, COSMOS_NVME_ADMIN_IDENTIFY,
                           6U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U);
    CHECK(cosmos_nvme_pcie_decode_admin(&raw, &admin) == COSMOS_OK);
    CHECK(admin.invalid_field == 1U);
    CHECK(admin.payload_bytes == 0U);
    return 0;
}

static int test_callback_pointer_guards(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;
    struct cosmos_nvme_command command;
    struct cosmos_nvme_completion completion;
    cosmos_nvme_pcie_media_io_fn saved_io;
    cosmos_nvme_pcie_media_flush_fn saved_flush;
    cosmos_nvme_pcie_media_zeroes_fn saved_zeroes;
    cosmos_nvme_pcie_media_deallocate_fn saved_deallocate;

    reset_media(&media);
    memset(&command, 0, sizeof(command));
    memset(&completion, 0, sizeof(completion));
    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);

    CHECK(service.adapter.post_completion(0, &completion) ==
          COSMOS_NVME_POST_HARD_FAILED);
    CHECK(service.adapter.post_completion(&bridge, 0) ==
          COSMOS_NVME_POST_HARD_FAILED);
    CHECK(service.adapter.post_completion(&bridge, &completion) ==
          COSMOS_NVME_POST_COMMITTED);

    CHECK(service.adapter.media_read(0, &command) == COSMOS_INVALID);
    saved_io = bridge.media_read;
    bridge.media_read = 0;
    CHECK(service.adapter.media_read(&bridge, &command) == COSMOS_INVALID);
    bridge.media_read = saved_io;
    CHECK(service.adapter.media_read(&bridge, &command) == COSMOS_OK);

    CHECK(service.adapter.media_program(0, &command) == COSMOS_INVALID);
    saved_io = bridge.media_program;
    bridge.media_program = 0;
    CHECK(service.adapter.media_program(&bridge, &command) == COSMOS_INVALID);
    bridge.media_program = saved_io;
    CHECK(service.adapter.media_program(&bridge, &command) == COSMOS_OK);

    CHECK(service.adapter.media_flush(0) == COSMOS_INVALID);
    saved_flush = bridge.media_flush;
    bridge.media_flush = 0;
    CHECK(service.adapter.media_flush(&bridge) == COSMOS_INVALID);
    bridge.media_flush = saved_flush;
    CHECK(service.adapter.media_flush(&bridge) == COSMOS_OK);

    CHECK(service.adapter.media_write_zeroes(0, &command) == COSMOS_INVALID);
    saved_zeroes = bridge.media_write_zeroes;
    bridge.media_write_zeroes = 0;
    CHECK(service.adapter.media_write_zeroes(&bridge, &command) ==
          COSMOS_INVALID);
    bridge.media_write_zeroes = saved_zeroes;
    CHECK(service.adapter.media_write_zeroes(&bridge, &command) == COSMOS_OK);

    CHECK(service.adapter.media_deallocate(0, &command) == COSMOS_INVALID);
    saved_deallocate = bridge.media_deallocate;
    bridge.media_deallocate = 0;
    CHECK(service.adapter.media_deallocate(&bridge, &command) ==
          COSMOS_INVALID);
    bridge.media_deallocate = saved_deallocate;
    CHECK(service.adapter.media_deallocate(&bridge, &command) == COSMOS_OK);
    return 0;
}

static int test_admin_adapter_and_dma_guards(void) {
    struct cosmos_nvme_admin_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct cosmos_nvme_admin_completion completion;
    struct cosmos_nvme_admin_command command;
    unsigned char payload[32];
    void *mapping;

    memset(&service, 0, sizeof(service));
    memset(&bridge, 0, sizeof(bridge));
    memset(&completion, 0, sizeof(completion));
    memset(&command, 0, sizeof(command));
    memset(payload, 0x5A, sizeof(payload));
    g_admin_init_result = COSMOS_OK;
    CHECK(cosmos_nvme_pcie_admin_service_init(
              0, &bridge, 1U, 0U, TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_admin_service_init(
              &service, 0, 1U, 0U, TEST_BLOCK_BYTES) == COSMOS_INVALID);
    CHECK(cosmos_nvme_pcie_admin_service_init(
              &service, &bridge, 1U, 0U, TEST_BLOCK_BYTES) == COSMOS_OK);
    g_admin_init_result = COSMOS_HW_ERROR;
    CHECK(cosmos_nvme_pcie_admin_service_init(
              &service, &bridge, 1U, 0U, TEST_BLOCK_BYTES) ==
          COSMOS_HW_ERROR);
    g_admin_init_result = COSMOS_OK;

    CHECK(cosmos_nvme_pcie_post_admin_completion(0, &completion) ==
          COSMOS_NVME_POST_HARD_FAILED);
    CHECK(cosmos_nvme_pcie_post_admin_completion(&bridge, 0) ==
          COSMOS_NVME_POST_HARD_FAILED);
    CHECK(cosmos_nvme_pcie_post_admin_completion(&bridge, &completion) ==
          COSMOS_NVME_POST_COMMITTED);
    CHECK(service.adapter.configure_io_sq(
              0, 1U, 1U, 1U, 2U, 3U, 4U) == COSMOS_INVALID);
    CHECK(service.adapter.configure_io_sq(
              &bridge, 1U, 1U, 1U, 2U, 3U, 4U) == COSMOS_OK);
    CHECK(service.adapter.configure_io_cq(
              0, 1U, 1U, 1U, 1U, 2U, 3U, 4U) == COSMOS_INVALID);
    CHECK(service.adapter.configure_io_cq(
              &bridge, 1U, 1U, 1U, 1U, 2U, 3U, 4U) == COSMOS_OK);
    CHECK(service.adapter.poll_async_event(&bridge, 0) == COSMOS_UNAVAILABLE);

    mapping = mmap((void *)(uintptr_t)COSMOS_NFC_DATA_POOL_BASE, 4096U,
                   PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    CHECK(mapping != MAP_FAILED);
    command.payload_address_low = 0x00200FF0U;
    command.payload_address_high = 1U;
    command.payload_address2_low = 0x00201000U;
    command.payload_address2_high = 1U;
    CHECK(service.adapter.write_payload(0, &command, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    CHECK(service.adapter.write_payload(&bridge, 0, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    CHECK(service.adapter.write_payload(&bridge, &command, 0, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 0U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);

    reset_dma();
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    reset_dma();
    g_dma_submit_results[0] = COSMOS_OK;
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    reset_dma();
    command.payload_address_low = 0x00200000U;
    g_dma_submit_results[0] = COSMOS_OK;
    g_dma_poll_results[0] = COSMOS_OK;
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 16U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED);
    reset_dma();
    command.payload_address_low = 0x00200FF0U;
    g_dma_submit_results[0] = COSMOS_OK;
    g_dma_poll_results[0] = COSMOS_OK;
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_HARD_FAILED);
    reset_dma();
    g_dma_submit_results[0] = COSMOS_OK;
    g_dma_submit_results[1] = COSMOS_OK;
    g_dma_poll_results[0] = COSMOS_OK;
    g_dma_poll_results[1] = COSMOS_OK;
    CHECK(service.adapter.write_payload(&bridge, &command, payload, 32U) ==
          COSMOS_NVME_ADMIN_PAYLOAD_COMMITTED);
    CHECK(munmap(mapping, 4096U) == 0);
    return 0;
}

static int test_precommit_retry_does_not_duplicate_media(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_pcie();
    reset_media(&media);
    g_pcie.commands[0] = make_raw_command(
        8U, 9U, 10U, COSMOS_NVME_OPCODE_WRITE, 0x2222U,
        COSMOS_NVME_NAMESPACE_ID, 0x00300000U, 0U, 0U, 0U,
        16U, 0U, 0U);
    g_pcie.command_count = 1U;
    g_pcie.post_results[0] = COSMOS_PCIE_NVME_COMPLETION_NOT_COMMITTED;
    g_pcie.post_results[1] = COSMOS_PCIE_NVME_COMPLETION_COMMITTED;
    g_pcie.post_result_count = 2U;

    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_RETRY);
    CHECK(media.program_calls == 1U);
    CHECK(g_pcie.fetch_index == 1U);
    CHECK(g_pcie.post_calls == 1U);
    CHECK(g_pcie.committed_count == 0U);
    CHECK(service.completion_state == COSMOS_NVME_COMPLETION_RETRY);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(media.program_calls == 1U);
    CHECK(g_pcie.fetch_index == 1U);
    CHECK(g_pcie.post_calls == 2U);
    CHECK(g_pcie.committed_count == 1U);
    CHECK(g_pcie.last_cid == 0x2222U);
    return 0;
}

static int test_queue_empty_and_budget(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;
    unsigned int index;

    reset_pcie();
    reset_media(&media);
    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(g_pcie.fetch_calls == 1U);
    CHECK(g_pcie.post_calls == 0U);

    reset_pcie();
    reset_media(&media);
    for (index = 0U; index < TEST_COMMAND_CAPACITY; ++index) {
        g_pcie.commands[index] = make_raw_command(
            index, index + 1U, index + 2U, COSMOS_NVME_OPCODE_FLUSH,
            0x3000U + index, COSMOS_NVME_NAMESPACE_ID, 0U, 0U, 0U, 0U,
            0U, 0U, 0U);
    }
    g_pcie.command_count = TEST_COMMAND_CAPACITY;
    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(g_pcie.fetch_index == COSMOS_NVME_SERVICE_BUDGET);
    CHECK(g_pcie.post_calls == COSMOS_NVME_SERVICE_BUDGET);
    CHECK(media.flush_calls == COSMOS_NVME_SERVICE_BUDGET);
    return 0;
}

static int test_ambiguous_completion_latches_without_retry(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_pcie();
    reset_media(&media);
    g_pcie.commands[0] = make_raw_command(
        1U, 2U, 3U, COSMOS_NVME_OPCODE_WRITE, 0x4000U,
        COSMOS_NVME_NAMESPACE_ID, 0x00300000U, 0U, 0U, 0U,
        24U, 0U, 0U);
    g_pcie.command_count = 1U;
    g_pcie.post_results[0] = COSMOS_PCIE_NVME_COMPLETION_AMBIGUOUS;
    g_pcie.post_result_count = 1U;

    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_COMPLETION_UNCERTAIN);
    CHECK(media.program_calls == 1U);
    CHECK(g_pcie.post_calls == 1U);
    CHECK(service.completion_state == COSMOS_NVME_COMPLETION_BLOCKED);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_COMPLETION_UNCERTAIN);
    CHECK(media.program_calls == 1U);
    CHECK(g_pcie.post_calls == 1U);
    return 0;
}

static int test_write_zeroes_and_dsm_decode(void) {
    struct cosmos_nvme_service service;
    struct cosmos_nvme_pcie_bridge bridge;
    struct media_mock media;

    reset_pcie();
    reset_media(&media);
    g_pcie.commands[0] = make_raw_command(
        1U, 2U, 3U, COSMOS_NVME_OPCODE_WRITE_ZEROES, 0x5000U,
        COSMOS_NVME_NAMESPACE_ID, 0U, 0U, 0U, 0U, 8U, 0U, 3U);
    g_pcie.commands[0].raw_dword[12] |= COSMOS_NVME_WRITE_ZEROES_LR |
        COSMOS_NVME_WRITE_ZEROES_FUA | COSMOS_NVME_WRITE_ZEROES_DEAC;
    g_pcie.commands[0].raw_dword[2] = 0x11223344U;
    g_pcie.commands[0].raw_dword[3] = 0x55667788U;
    g_pcie.commands[0].raw_dword[14] = 0x55667788U;
    g_pcie.commands[0].raw_dword[15] = 0x99AABBCCU;
    g_pcie.commands[1] = make_raw_command(
        1U, 3U, 4U, COSMOS_NVME_OPCODE_DATASET_MANAGEMENT, 0x5001U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200000U, 1U, 0U, 0U, 1U,
        COSMOS_NVME_DSM_ATTRIBUTE_MASK, 0U);
    g_pcie.command_count = 2U;
    CHECK(bridge_init(&service, &bridge, &media) == COSMOS_OK);
    CHECK(cosmos_nvme_service_poll(&service) == COSMOS_OK);
    CHECK(media.zeroes_calls == 1U);
    CHECK(media.deallocate_calls == 1U);
    CHECK(g_pcie.posted_sc[0] == COSMOS_NVME_SC_SUCCESS);
    CHECK(g_pcie.posted_sc[1] == COSMOS_NVME_SC_SUCCESS);
    return 0;
}

static int test_auto_dma_prp_and_control_contract(void) {
    struct cosmos_nvme_pcie_bridge bridge;
    struct cosmos_pcie_nvme_command raw;
    struct cosmos_nvme_admin_command admin;
    struct cosmos_nvme_command command;

    memset(&bridge, 0, sizeof(bridge));
    bridge.block_bytes = TEST_BLOCK_BYTES;

    raw = make_raw_command(
        1U, 2U, 3U, COSMOS_NVME_OPCODE_WRITE, 4U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200F00U, 1U,
        0x00800000U, 2U, 0U, 0U, 1U);
    raw.raw_dword[12] |= COSMOS_NVME_RW_FUA | COSMOS_NVME_RW_LR;
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    CHECK(command.opcode == COSMOS_NVME_OPCODE_WRITE);
    CHECK(command.data_address2_low == 0x00800000U);
    CHECK(command.data_address2_high == 2U);
    CHECK(command.control ==
          (COSMOS_NVME_RW_FUA | COSMOS_NVME_RW_LR));

    raw = make_raw_command(
        1U, 2U, 3U, COSMOS_NVME_OPCODE_READ, 5U,
        COSMOS_NVME_NAMESPACE_ID, 0x00200F00U, 1U,
        0x00900010U, 2U, 0U, 0U, 15U);
    CHECK(cosmos_nvme_pcie_decode_io(&bridge, &raw, &command) == COSMOS_OK);
    CHECK(command.opcode == COSMOS_NVME_OPCODE_READ);
    CHECK(command.data_bytes == 8192U);
    CHECK(command.data_address2_low == 0x00900010U);

    raw = make_raw_command(
        0U, 2U, 3U, COSMOS_NVME_ADMIN_IDENTIFY, 6U, 0U,
        0x00200F00U, 1U, 0x00A00000U, 2U, 0U, 0U, 0U);
    raw.raw_dword[10] = COSMOS_NVME_ADMIN_IDENTIFY_CONTROLLER;
    CHECK(cosmos_nvme_pcie_decode_admin(&raw, &admin) == COSMOS_OK);
    CHECK(admin.invalid_field == 0U);
    CHECK(admin.payload_address2_low == 0x00A00000U);
    CHECK(admin.payload_address2_high == 2U);
    return 0;
}

int main(void) {
#if defined(COSMOS_NVME_PCIE_ADAPTER_COVERAGE_ONLY)
    CHECK(test_auto_dma_prp_and_control_contract() == 0);
    CHECK(test_pointer_and_scalar_marshalling_edges() == 0);
    CHECK(test_callback_pointer_guards() == 0);
    CHECK(test_admin_adapter_and_dma_guards() == 0);
    CHECK(test_init_rejects_missing_media() == 0);
    puts("cosmos NVMe PCIe adapter contract: PASS");
#elif defined(COSMOS_NVME_PRP_CONTROL_ONLY)
    CHECK(test_auto_dma_prp_and_control_contract() == 0);
    puts("cosmos NVMe PRP/control contract: PASS");
#else
    CHECK(test_auto_dma_prp_and_control_contract() == 0);
    CHECK(test_pointer_and_scalar_marshalling_edges() == 0);
    CHECK(test_callback_pointer_guards() == 0);
    CHECK(test_admin_adapter_and_dma_guards() == 0);
    CHECK(test_exact_decode_and_forwarding() == 0);
    CHECK(test_prp2_and_sgl_validation() == 0);
    CHECK(test_init_rejects_missing_media() == 0);
    CHECK(test_precommit_retry_does_not_duplicate_media() == 0);
    CHECK(test_queue_empty_and_budget() == 0);
    CHECK(test_ambiguous_completion_latches_without_retry() == 0);
    CHECK(test_write_zeroes_and_dsm_decode() == 0);
    puts("cosmos NVMe PCIe adapter contract: PASS");
#endif
    return 0;
}
