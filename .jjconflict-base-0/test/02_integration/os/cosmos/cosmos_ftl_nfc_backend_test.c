#define _GNU_SOURCE

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "cosmos_ftl_nfc_backend.h"
#if defined(COSMOS_NVME_FTL_PHYSICAL_COMPOSITION_TEST)
#include "cosmos_nvme_ftl_media.h"
#endif

#define CHECK(condition)                                                     \
    do {                                                                      \
        if (!(condition)) {                                                   \
            fprintf(stderr, "%s:%d: check failed: %s\n",                    \
                    __FILE__, __LINE__, #condition);                         \
            return 1;                                                         \
        }                                                                     \
    } while (0)

#define TEST_L2P_COUNT 8U
#define TEST_BLOCK_COUNT 4U
#define TEST_JOURNAL_PAGES 256U
#define TEST_MAX_PAGES 1024U

static unsigned char metadata_dma[COSMOS_NFC_PAGE_DATA_BYTES]
    __attribute__((aligned(COSMOS_NFC_PAGE_DATA_BYTES)));
static unsigned char data_dma[COSMOS_NFC_PAGE_DATA_BYTES]
    __attribute__((aligned(COSMOS_NFC_PAGE_DATA_BYTES)));
static unsigned char spare_dma[COSMOS_NFC_PAGE_SPARE_BYTES]
    __attribute__((aligned(COSMOS_NFC_PAGE_SPARE_BYTES)));
static unsigned int error_dma[COSMOS_NFC_ERROR_INFO_WORDS];
static unsigned int completion_dma;
static unsigned int status_dma;

struct mock_page {
    unsigned int used;
    unsigned int channel;
    unsigned int way;
    unsigned int row;
    unsigned char data[COSMOS_NFC_PAGE_DATA_BYTES];
    unsigned char spare[COSMOS_NFC_PAGE_SPARE_BYTES];
};

struct mock_nfc {
    struct mock_page page[TEST_MAX_PAGES];
    unsigned int program_calls;
    unsigned int erase_calls;
};

static struct mock_nfc mock_storage;
static int forced_read_status;
static unsigned int mock_needs_refresh;

#if defined(COSMOS_NVME_FTL_PHYSICAL_COMPOSITION_TEST)
static int mock_read(void *context, const struct cosmos_nfc_io *io,
                     struct cosmos_nfc_ecc *ecc);
static int mock_program(void *context, const struct cosmos_nfc_io *io);
static unsigned char host_dma[COSMOS_FTL_NVME_BLOCK_BYTES];
static unsigned int composition_l2p[8U];
static struct cosmos_ftl_block composition_blocks[COSMOS_FTL_BLOCK_COUNT];
#if defined(COSMOS_NVME_FTL_ECC_REFRESH_TEST)
static unsigned int recovered_l2p[8U];
static struct cosmos_ftl_block recovered_blocks[COSMOS_FTL_BLOCK_COUNT];
#endif

int cosmos_test_media_dma_h2d(unsigned int slot, unsigned int offset,
                              unsigned int device_address) {
    CHECK(slot == 9U && offset == 0U);
    memcpy((void *)(uintptr_t)device_address, host_dma, sizeof(host_dma));
    return COSMOS_OK;
}

int cosmos_test_media_dma_d2h(unsigned int slot, unsigned int offset,
                              unsigned int device_address) {
    CHECK(slot == 9U && offset == 0U);
    memcpy(host_dma, (const void *)(uintptr_t)device_address,
           sizeof(host_dma));
    return COSMOS_OK;
}

int cosmos_test_media_dma_poll(
    enum cosmos_pcie_host_dma_direction direction) {
    CHECK(direction == COSMOS_PCIE_HOST_TO_DEVICE ||
          direction == COSMOS_PCIE_DEVICE_TO_HOST);
    return COSMOS_OK;
}

int cosmos_test_media_nfc_read(const struct cosmos_nfc_io *io,
                               struct cosmos_nfc_ecc *ecc) {
    return mock_read(&mock_storage, io, ecc);
}

int cosmos_test_media_nfc_program(const struct cosmos_nfc_io *io) {
    return mock_program(&mock_storage, io);
}
#endif

static unsigned int page_key(const struct cosmos_nfc_io *io) {
    return (io->channel << 28U) ^ (io->way << 24U) ^ io->row_address;
}

static struct mock_page *find_page(struct mock_nfc *mock,
                                   const struct cosmos_nfc_io *io) {
    unsigned int key = page_key(io);
    unsigned int index;

    for (index = 0U; index < TEST_MAX_PAGES; ++index) {
        if (mock->page[index].used != 0U &&
            page_key(&(struct cosmos_nfc_io){
                .channel = mock->page[index].channel,
                .way = mock->page[index].way,
                .row_address = mock->page[index].row}) == key) {
            return &mock->page[index];
        }
    }
    return 0;
}

static int mock_read(void *context, const struct cosmos_nfc_io *io,
                     struct cosmos_nfc_ecc *ecc) {
    struct mock_nfc *mock = context;
    struct mock_page *page = find_page(mock, io);

    memset((void *)(uintptr_t)io->data_address, 0xFF,
           COSMOS_NFC_PAGE_DATA_BYTES);
    memset((void *)(uintptr_t)io->spare_address, 0xFF,
           COSMOS_NFC_PAGE_SPARE_BYTES);
    if (ecc != 0) {
        memset(ecc, 0, sizeof(*ecc));
    }
    if (forced_read_status != COSMOS_OK) {
        return forced_read_status;
    }
    if (page == 0) {
        return COSMOS_OK;
    }
    memcpy((void *)(uintptr_t)io->data_address, page->data,
           COSMOS_NFC_PAGE_DATA_BYTES);
    memcpy((void *)(uintptr_t)io->spare_address, page->spare,
           COSMOS_NFC_PAGE_SPARE_BYTES);
    if (ecc != 0) {
        ecc->crc_valid = 1U;
        ecc->spare_valid = 1U;
        ecc->page_valid = 1U;
        ecc->worst_chunk_errors = 0U;
        ecc->needs_refresh = mock_needs_refresh;
    }
    return COSMOS_OK;
}

static int mock_program(void *context, const struct cosmos_nfc_io *io) {
    struct mock_nfc *mock = context;
    struct mock_page *page = find_page(mock, io);
    unsigned int index;

    if (page != 0) {
        return COSMOS_HW_ERROR;
    }
    for (index = 0U; index < TEST_MAX_PAGES; ++index) {
        if (mock->page[index].used == 0U) {
            page = &mock->page[index];
            page->used = 1U;
            page->channel = io->channel;
            page->way = io->way;
            page->row = io->row_address;
            memcpy(page->data, (const void *)(uintptr_t)io->data_address,
                   COSMOS_NFC_PAGE_DATA_BYTES);
            memcpy(page->spare, (const void *)(uintptr_t)io->spare_address,
                   COSMOS_NFC_PAGE_SPARE_BYTES);
            ++mock->program_calls;
            return COSMOS_OK;
        }
    }
    return COSMOS_UNAVAILABLE;
}

static int mock_erase(void *context, unsigned int channel, unsigned int way,
                      unsigned int row, unsigned int status_report_address) {
    struct mock_nfc *mock = context;
    unsigned int index;

    (void)status_report_address;
    ++mock->erase_calls;
    for (index = 0U; index < TEST_MAX_PAGES; ++index) {
        if (mock->page[index].used != 0U &&
            mock->page[index].channel == channel &&
            mock->page[index].way == way &&
            mock->page[index].row >= row &&
            mock->page[index].row < row + COSMOS_NFC_ROWS_PER_BLOCK) {
            mock->page[index].used = 0U;
        }
    }
    return COSMOS_OK;
}

unsigned int cosmos_mmio_test_read32(unsigned int address) {
    (void)address;
    return 0U;
}

void cosmos_mmio_test_write32(unsigned int address, unsigned int value) {
    (void)address;
    (void)value;
}

static int make_ppa(unsigned int die, unsigned int lun, unsigned int block,
                    unsigned int page, unsigned int *ppa) {
    return cosmos_ftl_ppa_encode(die, lun, block, page, ppa);
}

#if defined(COSMOS_NVME_FTL_PHYSICAL_COMPOSITION_TEST)
static int composition_test(void) {
    const struct cosmos_ftl_nfc_dma dma = {
        .metadata_address = (unsigned int)(uintptr_t)metadata_dma,
        .payload_address = (unsigned int)(uintptr_t)data_dma,
        .spare_address = (unsigned int)(uintptr_t)spare_dma,
        .error_info_address = (unsigned int)(uintptr_t)error_dma,
        .completion_address = (unsigned int)(uintptr_t)&completion_dma,
        .status_report_address = (unsigned int)(uintptr_t)&status_dma
    };
    const struct cosmos_ftl_nfc_ops ops = {
        &mock_storage, mock_read, mock_program, mock_erase
    };
    struct cosmos_ftl_nfc_backend backend;
    struct cosmos_ftl ftl;
    struct cosmos_nvme_ftl_media media;
    struct cosmos_nvme_command command;
#if defined(COSMOS_NVME_FTL_ECC_REFRESH_TEST)
    struct cosmos_ftl_nfc_backend recovered_backend;
    struct cosmos_ftl recovered_ftl;
    struct cosmos_nvme_ftl_media recovered_media;
    unsigned int recovered_ppa;
    unsigned int destination;
#endif
    unsigned int mapped_after;
    unsigned int mapped_before;
    unsigned int index;

    memset(&mock_storage, 0, sizeof(mock_storage));
    CHECK(cosmos_ftl_nfc_backend_init(
        &backend, &dma, &ops, 8U, COSMOS_FTL_BLOCK_COUNT, 256ULL) ==
        COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_format(&backend) == COSMOS_OK);
    CHECK(cosmos_ftl_init(
        &ftl, &backend.ftl, composition_l2p, 8U, composition_blocks,
        COSMOS_FTL_BLOCK_COUNT) == COSMOS_OK);
    CHECK(cosmos_ftl_factory_initialize_erased(&ftl) == COSMOS_OK);
    CHECK(cosmos_nvme_ftl_media_init(
        &media, &ftl, dma.payload_address, dma.spare_address,
        dma.completion_address, dma.status_report_address,
        dma.error_info_address) == COSMOS_OK);

    memset(&command, 0, sizeof(command));
    command.slot_tag = 9U;
    command.namespace_id = COSMOS_NVME_NAMESPACE_ID;
    command.opcode = COSMOS_NVME_OPCODE_WRITE;
    command.data_address_low = 0x1000U;
    command.data_bytes = COSMOS_FTL_NVME_BLOCK_BYTES;
    memset(host_dma, 0x5AU, sizeof(host_dma));
    CHECK(cosmos_nvme_ftl_media_program(&media, &command) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(&ftl, 0U, &mapped_before) == COSMOS_OK);

    memset(host_dma, 0U, sizeof(host_dma));
    command.opcode = COSMOS_NVME_OPCODE_READ;
#if defined(COSMOS_NVME_FTL_ECC_REFRESH_TEST)
    mock_needs_refresh = 1U;
#endif
    CHECK(cosmos_nvme_ftl_media_read(&media, &command) == COSMOS_OK);
    mock_needs_refresh = 0U;
    for (index = 0U; index < sizeof(host_dma); ++index) {
        CHECK(host_dma[index] == 0x5AU);
    }
#if defined(COSMOS_NVME_FTL_ECC_REFRESH_TEST)
    CHECK(cosmos_ftl_lookup(&ftl, 0U, &mapped_after) == COSMOS_OK);
    CHECK(mapped_after != mapped_before);

    memset(host_dma, 0U, sizeof(host_dma));
    CHECK(cosmos_nvme_ftl_media_read(&media, &command) == COSMOS_OK);
    for (index = 0U; index < sizeof(host_dma); ++index) {
        CHECK(host_dma[index] == 0x5AU);
    }
    CHECK(cosmos_ftl_refresh_page(
        &ftl, 0U, mapped_before, &destination) == COSMOS_INVALID);
    CHECK(cosmos_ftl_lookup(&ftl, 0U, &destination) == COSMOS_OK);
    CHECK(destination == mapped_after);

    forced_read_status = COSMOS_HW_ERROR;
    CHECK(cosmos_ftl_refresh_page(
        &ftl, 0U, mapped_after, &destination) == COSMOS_HW_ERROR);
    forced_read_status = COSMOS_OK;
    CHECK(cosmos_ftl_lookup(&ftl, 0U, &destination) == COSMOS_OK);
    CHECK(destination == mapped_after);

    CHECK(cosmos_ftl_nfc_backend_init(
        &recovered_backend, &dma, &ops, 8U, COSMOS_FTL_BLOCK_COUNT,
        256ULL) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_mount(&recovered_backend) == COSMOS_OK);
    CHECK(cosmos_ftl_init(
        &recovered_ftl, &recovered_backend.ftl, recovered_l2p, 8U,
        recovered_blocks, COSMOS_FTL_BLOCK_COUNT) == COSMOS_OK);
    CHECK(cosmos_ftl_recover(&recovered_ftl) == COSMOS_OK);
    CHECK(cosmos_ftl_lookup(
        &recovered_ftl, 0U, &recovered_ppa) == COSMOS_OK);
    CHECK(recovered_ppa == mapped_after);
    CHECK(cosmos_nvme_ftl_media_init(
        &recovered_media, &recovered_ftl, dma.payload_address,
        dma.spare_address, dma.completion_address, dma.status_report_address,
        dma.error_info_address) == COSMOS_OK);
    memset(host_dma, 0U, sizeof(host_dma));
    CHECK(cosmos_nvme_ftl_media_read(
        &recovered_media, &command) == COSMOS_OK);
    for (index = 0U; index < sizeof(host_dma); ++index) {
        CHECK(host_dma[index] == 0x5AU);
    }
    puts("cosmos NVMe ECC refresh relocation: PASS");
#else
    (void)mapped_after;
    puts("cosmos NVMe physical media composition: PASS");
#endif
    return 0;
}
#endif

#if defined(COSMOS_FTL_NFC_IO_FAIL_CLOSED_TEST)
static int io_fail_closed_test(void) {
    const struct cosmos_ftl_nfc_dma dma = {
        .metadata_address = (unsigned int)(uintptr_t)metadata_dma,
        .payload_address = (unsigned int)(uintptr_t)data_dma,
        .spare_address = (unsigned int)(uintptr_t)spare_dma,
        .error_info_address = (unsigned int)(uintptr_t)error_dma,
        .completion_address = (unsigned int)(uintptr_t)&completion_dma,
        .status_report_address = (unsigned int)(uintptr_t)&status_dma
    };
    const struct cosmos_ftl_nfc_ops ops = {
        &mock_storage, mock_read, mock_program, mock_erase
    };
    struct cosmos_ftl_nfc_backend backend;
    struct cosmos_ftl_nfc_backend remounted;

    memset(&mock_storage, 0, sizeof(mock_storage));
    forced_read_status = COSMOS_OK;
    CHECK(cosmos_ftl_nfc_backend_init(
        &backend, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_format(&backend) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_init(
        &remounted, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    forced_read_status = COSMOS_TIMEOUT;
    CHECK(cosmos_ftl_nfc_backend_mount(&remounted) == COSMOS_HW_ERROR);
    forced_read_status = COSMOS_RETRY;
    CHECK(cosmos_ftl_nfc_backend_mount(&remounted) == COSMOS_RETRY);
    forced_read_status = COSMOS_OK;
    CHECK(cosmos_ftl_nfc_backend_mount(&remounted) == COSMOS_OK);
    puts("cosmos FTL NFC IO fail-closed: PASS");
    return 0;
}
#endif

#if defined(COSMOS_FTL_NFC_DMA_ISOLATION_TEST)
static int dma_isolation_test(void) {
    const struct cosmos_ftl_nfc_dma dma = {
        .metadata_address = (unsigned int)(uintptr_t)metadata_dma,
        .payload_address = (unsigned int)(uintptr_t)data_dma,
        .spare_address = (unsigned int)(uintptr_t)spare_dma,
        .error_info_address = (unsigned int)(uintptr_t)error_dma,
        .completion_address = (unsigned int)(uintptr_t)&completion_dma,
        .status_report_address = (unsigned int)(uintptr_t)&status_dma
    };
    const struct cosmos_ftl_nfc_ops ops = {
        &mock_storage, mock_read, mock_program, mock_erase
    };
    struct cosmos_ftl_nfc_backend backend;
    struct cosmos_ftl_journal_record record;
    struct mock_page *page;
    unsigned int ppa;
    unsigned int channel;
    unsigned int way;
    unsigned int row;
    unsigned int index;

    memset(&mock_storage, 0, sizeof(mock_storage));
    CHECK(cosmos_ftl_nfc_backend_init(
        &backend, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_format(&backend) == COSMOS_OK);
    memset(data_dma, 0x5AU, sizeof(data_dma));
    memset(&record, 0, sizeof(record));
    record.magic = COSMOS_FTL_MAGIC;
    record.type = COSMOS_FTL_RECORD_ALLOCATE;
    record.new_ppa = 1U;
    record.old_ppa = COSMOS_FTL_PPA_NONE;
    record.crc = cosmos_ftl_journal_record_crc(&record);
    CHECK(backend.ftl.append_journal(
        &backend, 0ULL, &record) == COSMOS_FTL_APPEND_COMMITTED);
    for (index = 0U; index < sizeof(data_dma); ++index) {
        CHECK(data_dma[index] == 0x5AU);
    }
    CHECK(make_ppa(
        0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 0U, &ppa) == COSMOS_OK);
    CHECK(backend.ftl.program_data(&backend, ppa, 0U, 1ULL) == COSMOS_OK);
    CHECK(cosmos_ftl_ppa_row(ppa, &channel, &way, &row) == COSMOS_OK);
    page = find_page(&mock_storage, &(struct cosmos_nfc_io){
        .channel = channel, .way = way, .row_address = row});
    CHECK(page != 0);
    for (index = 0U; index < sizeof(data_dma); ++index) {
        CHECK(page->data[index] == 0x5AU);
    }
    puts("cosmos FTL NFC metadata/payload DMA isolation: PASS");
    return 0;
}
#endif

static int metadata_ppa(unsigned int page, unsigned int *ppa) {
    unsigned int lane = page / COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE;
    unsigned int in_lane = page % COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE;

    return cosmos_ftl_ppa_encode(
        lane / COSMOS_FTL_LUN_COUNT,
        lane % COSMOS_FTL_LUN_COUNT,
        in_lane / COSMOS_FTL_PAGES_PER_BLOCK,
        in_lane % COSMOS_FTL_PAGES_PER_BLOCK, ppa);
}

static int main_test(void) {
    const struct cosmos_ftl_nfc_dma dma = {
        .metadata_address = (unsigned int)(uintptr_t)metadata_dma,
        .payload_address = (unsigned int)(uintptr_t)data_dma,
        .spare_address = (unsigned int)(uintptr_t)spare_dma,
        .error_info_address = (unsigned int)(uintptr_t)error_dma,
        .completion_address = (unsigned int)(uintptr_t)&completion_dma,
        .status_report_address = (unsigned int)(uintptr_t)&status_dma
    };
    const struct cosmos_ftl_nfc_ops ops = {
        &mock_storage, mock_read, mock_program, mock_erase
    };
    struct cosmos_ftl_nfc_backend backend;
    struct cosmos_ftl_nfc_backend remounted;
    struct cosmos_ftl_nfc_backend replayed;
    unsigned int l2p[TEST_L2P_COUNT];
    unsigned int loaded_l2p[TEST_L2P_COUNT];
    struct cosmos_ftl_block blocks[TEST_BLOCK_COUNT];
    struct cosmos_ftl_block loaded_blocks[TEST_BLOCK_COUNT];
    struct cosmos_ftl_checkpoint checkpoint;
    struct cosmos_ftl_journal_record record;
    unsigned int ppa;
    unsigned int source_ppa;
    unsigned int destination_ppa;
    unsigned int channel;
    unsigned int way;
    unsigned int row;
    unsigned int lpn;
    unsigned int needs_refresh;
    unsigned int index;
    unsigned int byte;
    unsigned int previous_crc = 0U;
    unsigned long long generation;
    struct mock_page *page;

    memset(&mock_storage, 0, sizeof(mock_storage));
    memset(l2p, 0xA5, sizeof(l2p));
    memset(blocks, 0x5A, sizeof(blocks));
    CHECK((uintptr_t)data_dma <= UINT32_MAX);
    CHECK((uintptr_t)metadata_dma <= UINT32_MAX);
    CHECK((uintptr_t)spare_dma <= UINT32_MAX);
    CHECK((uintptr_t)error_dma <= UINT32_MAX);
    CHECK((uintptr_t)&completion_dma <= UINT32_MAX);
    CHECK((uintptr_t)&status_dma <= UINT32_MAX);
    CHECK(cosmos_ftl_nfc_backend_init(
        &backend, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    CHECK(backend.ftl.journal_capacity == TEST_JOURNAL_PAGES);
    CHECK(cosmos_ftl_nfc_backend_format(&backend) == COSMOS_OK);
    CHECK(mock_storage.erase_calls == COSMOS_FTL_METADATA_BLOCK_COUNT);
    CHECK(mock_storage.program_calls == 1U);
    CHECK(mock_storage.page[0].data[0] == 0x31U);
    CHECK(mock_storage.page[0].data[1] == 0x4EU);
    CHECK(mock_storage.page[0].data[2] == 0x46U);
    CHECK(mock_storage.page[0].data[3] == 0x43U);

    CHECK(cosmos_ftl_nfc_backend_init(
        &remounted, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_mount(&remounted) == COSMOS_OK);

    CHECK(make_ppa(0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 0U,
                   &source_ppa) ==
          COSMOS_OK);
    CHECK(make_ppa(0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 1U,
                   &destination_ppa) == COSMOS_OK);
    memset(data_dma, 0xA7, sizeof(data_dma));
    CHECK(remounted.ftl.program_data(
        &remounted, source_ppa, 3U, 9ULL) == COSMOS_OK);
    CHECK(remounted.ftl.read_page_tag(
        &remounted, source_ppa, &lpn, &generation,
        &needs_refresh) == COSMOS_OK);
    CHECK(lpn == 3U && generation == 9ULL && needs_refresh == 0U);
    CHECK(remounted.ftl.program_data(
        &remounted, source_ppa, 3U, 10ULL) != COSMOS_OK);
    CHECK(remounted.ftl.copy_data(
        &remounted, source_ppa, destination_ppa, 3U, 10ULL) == COSMOS_OK);
    CHECK(remounted.ftl.read_page_tag(
        &remounted, destination_ppa, &lpn, &generation,
        &needs_refresh) == COSMOS_OK);
    CHECK(lpn == 3U && generation == 10ULL && needs_refresh == 0U);

    CHECK(cosmos_ftl_ppa_row(
        source_ppa, &channel, &way, &row) == COSMOS_OK);
    page = find_page(&mock_storage, &(struct cosmos_nfc_io){
        .channel = channel, .way = way, .row_address = row});
    CHECK(page != 0);
    for (byte = 0U; byte < COSMOS_NFC_PAGE_DATA_BYTES; ++byte) {
        CHECK(page->data[byte] == 0xA7U);
    }
    page->spare[0] ^= 1U;
    CHECK(remounted.ftl.read_page_tag(
        &remounted, source_ppa, &lpn, &generation,
        &needs_refresh) == COSMOS_HW_ERROR);
    page->spare[0] ^= 1U;

    for (index = 0U; index < 128U; ++index) {
        memset(&record, 0, sizeof(record));
        record.magic = COSMOS_FTL_MAGIC;
        record.type = COSMOS_FTL_RECORD_MAP;
        record.sequence = index;
        record.generation = index + 1ULL;
        record.lpn = index % TEST_L2P_COUNT;
        record.new_ppa = 0x100U + index;
        record.previous_crc = previous_crc;
        record.crc = cosmos_ftl_journal_record_crc(&record);
        previous_crc = record.crc;
        CHECK(remounted.ftl.append_journal(
            &remounted, index, &record) == COSMOS_FTL_APPEND_COMMITTED);
    }
    CHECK(metadata_ppa(
        remounted.journal_start_page + 127U, &ppa) == COSMOS_OK);
    CHECK(cosmos_ftl_ppa_row(ppa, &channel, &way, &row) == COSMOS_OK);
    page = find_page(&mock_storage, &(struct cosmos_nfc_io){
        .channel = channel, .way = way, .row_address = row});
    CHECK(page != 0);
    page->data[40] ^= 1U;
    CHECK(remounted.ftl.read_journal(
        &remounted, 127ULL, &record) == COSMOS_INVALID);
    page->data[40] ^= 1U;

    memset(&checkpoint, 0, sizeof(checkpoint));
    checkpoint.magic = COSMOS_FTL_MAGIC;
    checkpoint.version = COSMOS_FTL_VERSION;
    checkpoint.generation = 1ULL;
    checkpoint.journal_index = 128ULL;
    checkpoint.l2p_count = TEST_L2P_COUNT;
    checkpoint.block_count = TEST_BLOCK_COUNT;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 0U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    CHECK(remounted.ftl.trim_journal(&remounted, 128ULL) ==
          COSMOS_UNAVAILABLE);
    checkpoint.generation = 2ULL;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 1U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    CHECK(remounted.ftl.trim_journal(&remounted, 128ULL) == COSMOS_OK);
    CHECK(mock_storage.erase_calls == COSMOS_FTL_METADATA_BLOCK_COUNT + 1U);
    CHECK(remounted.ftl.read_journal(
        &remounted, 0ULL, &record) == COSMOS_UNAVAILABLE);
    memset(&record, 0, sizeof(record));
    record.magic = COSMOS_FTL_MAGIC;
    record.type = COSMOS_FTL_RECORD_MAP;
    record.sequence = 128ULL;
    record.generation = 129ULL;
    record.lpn = 2U;
    record.new_ppa = 0x200U;
    record.previous_crc = previous_crc;
    record.crc = cosmos_ftl_journal_record_crc(&record);
    CHECK(remounted.ftl.append_journal(
        &remounted, 128ULL, &record) == COSMOS_FTL_APPEND_COMMITTED);
    previous_crc = record.crc;
    CHECK(cosmos_ftl_nfc_backend_init(
        &replayed, &dma, &ops, TEST_L2P_COUNT, TEST_BLOCK_COUNT,
        TEST_JOURNAL_PAGES) == COSMOS_OK);
    CHECK(cosmos_ftl_nfc_backend_mount(&replayed) == COSMOS_OK);
    CHECK(replayed.ftl.read_checkpoint_header(
        &replayed, 0U, &checkpoint) == COSMOS_OK);
    CHECK(replayed.ftl.read_checkpoint_header(
        &replayed, 1U, &checkpoint) == COSMOS_OK);
    CHECK(replayed.ftl.read_journal(
        &replayed, 128ULL, &record) == COSMOS_OK);
    CHECK(record.sequence == 128ULL && replayed.journal_next_index == 129ULL);
#if defined(COSMOS_FTL_NFC_RECOVERY_WRAP_TEST)
    for (index = 129U; index < 256U; ++index) {
        memset(&record, 0, sizeof(record));
        record.magic = COSMOS_FTL_MAGIC;
        record.type = COSMOS_FTL_RECORD_MAP;
        record.sequence = index;
        record.generation = index + 1ULL;
        record.lpn = index % TEST_L2P_COUNT;
        record.new_ppa = 0x300U + index;
        record.previous_crc = previous_crc;
        record.crc = cosmos_ftl_journal_record_crc(&record);
        previous_crc = record.crc;
        CHECK(remounted.ftl.append_journal(
            &remounted, index, &record) == COSMOS_FTL_APPEND_COMMITTED);
    }
    checkpoint.journal_index = 256ULL;
    checkpoint.generation = 256ULL;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 0U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    checkpoint.generation++;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 1U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    CHECK(remounted.ftl.trim_journal(&remounted, 256ULL) == COSMOS_OK);
    for (index = 256U; index < 384U; ++index) {
        memset(&record, 0, sizeof(record));
        record.magic = COSMOS_FTL_MAGIC;
        record.type = COSMOS_FTL_RECORD_MAP;
        record.sequence = index;
        record.generation = index + 1ULL;
        record.lpn = index % TEST_L2P_COUNT;
        record.new_ppa = 0x400U + index;
        record.previous_crc = previous_crc;
        record.crc = cosmos_ftl_journal_record_crc(&record);
        previous_crc = record.crc;
        CHECK(remounted.ftl.append_journal(
            &remounted, index, &record) == COSMOS_FTL_APPEND_COMMITTED);
    }
    checkpoint.journal_index = 384ULL;
    checkpoint.generation = 384ULL;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 0U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    checkpoint.generation++;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 1U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    CHECK(remounted.ftl.trim_journal(&remounted, 384ULL) == COSMOS_OK);
    memset(&record, 0, sizeof(record));
    record.magic = COSMOS_FTL_MAGIC;
    record.type = COSMOS_FTL_RECORD_MAP;
    record.sequence = 384ULL;
    record.generation = 385ULL;
    record.lpn = 0U;
    record.new_ppa = 0x600U;
    record.previous_crc = previous_crc;
    record.crc = cosmos_ftl_journal_record_crc(&record);
    CHECK(remounted.ftl.append_journal(
        &remounted, 384ULL, &record) == COSMOS_FTL_APPEND_COMMITTED);
#endif
    CHECK(remounted.ftl.read_checkpoint_data(
        &remounted, 1U, loaded_l2p, TEST_L2P_COUNT, loaded_blocks,
        TEST_BLOCK_COUNT) == COSMOS_OK);
    CHECK(memcmp(l2p, loaded_l2p, sizeof(l2p)) == 0);
    CHECK(memcmp(blocks, loaded_blocks, sizeof(blocks)) == 0);
#if defined(COSMOS_FTL_NFC_TEST_SMALL_GEOMETRY) && \
    !defined(COSMOS_FTL_NFC_RECOVERY_WRAP_TEST)
    for (index = 0U; index < 127U; ++index) {
        checkpoint.generation = 3ULL + index;
        CHECK(remounted.ftl.write_checkpoint(
            &remounted, 0U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
            &checkpoint) == COSMOS_OK);
    }
    checkpoint.generation = 1000ULL;
    CHECK(remounted.ftl.write_checkpoint(
        &remounted, 0U, l2p, TEST_L2P_COUNT, blocks, TEST_BLOCK_COUNT,
        &checkpoint) == COSMOS_OK);
    CHECK(mock_storage.erase_calls == COSMOS_FTL_METADATA_BLOCK_COUNT + 3U);
#endif
#if defined(COSMOS_FTL_NFC_RECOVERY_WRAP_TEST)
    puts("cosmos FTL NFC recovery and wrap: PASS");
#else
    puts("cosmos FTL NFC persistence backend: PASS");
#endif
    return 0;
}

int main(void) {
#if defined(COSMOS_NVME_FTL_PHYSICAL_COMPOSITION_TEST)
    return composition_test();
#elif defined(COSMOS_FTL_NFC_IO_FAIL_CLOSED_TEST)
    return io_fail_closed_test();
#elif defined(COSMOS_FTL_NFC_DMA_ISOLATION_TEST)
    return dma_isolation_test();
#else
    return main_test();
#endif
}
