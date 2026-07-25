#define _GNU_SOURCE

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#include "cosmos_nvme_ftl_media.h"

#define DATA_ADDRESS 0x10000000U
#define SPARE_ADDRESS 0x11100000U
#define COMPLETION_ADDRESS 0x17000000U
#define STATUS_ADDRESS 0x17001000U
#define ERROR_ADDRESS 0x17002000U
#define HOST_BYTES (COSMOS_PCIE_HOST_DMA_AUTO_OFFSET_MAX + 1U) * 4096U

static unsigned char host_data[HOST_BYTES];
static unsigned char programmed_page[COSMOS_NFC_PAGE_DATA_BYTES];
static unsigned int dma_h2d_calls;
static unsigned int dma_d2h_calls;
static unsigned int nfc_read_calls;
static unsigned int nfc_program_calls;
static unsigned int nfc_read_attempts;
static unsigned int nfc_read_retry_remaining;

int cosmos_test_dma_h2d(unsigned int slot, unsigned int offset,
                        unsigned int device_address) {
    assert(slot == 9U);
    assert(offset * 4096U + 4096U <= HOST_BYTES);
    memcpy((void *)(uintptr_t)device_address, host_data + offset * 4096U,
           4096U);
    dma_h2d_calls++;
    return COSMOS_OK;
}

int cosmos_test_dma_d2h(unsigned int slot, unsigned int offset,
                        unsigned int device_address) {
    assert(slot == 9U);
    assert(offset * 4096U + 4096U <= HOST_BYTES);
    memcpy(host_data + offset * 4096U, (void *)(uintptr_t)device_address,
           4096U);
    dma_d2h_calls++;
    return COSMOS_OK;
}

int cosmos_test_dma_poll(enum cosmos_pcie_host_dma_direction direction) {
    assert(direction == COSMOS_PCIE_HOST_TO_DEVICE ||
           direction == COSMOS_PCIE_DEVICE_TO_HOST);
    return COSMOS_OK;
}

int cosmos_test_nfc_read(const struct cosmos_nfc_io *io,
                         struct cosmos_nfc_ecc *ecc) {
    unsigned int index;

    assert(io->data_address == DATA_ADDRESS);
    nfc_read_attempts++;
    if (nfc_read_retry_remaining != 0U) {
        nfc_read_retry_remaining--;
        return COSMOS_RETRY;
    }
    for (index = 0U; index < COSMOS_NFC_PAGE_DATA_BYTES; ++index) {
        ((unsigned char *)(uintptr_t)io->data_address)[index] =
            (unsigned char)(0xA0U + (index & 0x0FU));
    }
    memset((void *)(uintptr_t)io->spare_address, 0x5A,
           COSMOS_NFC_PAGE_SPARE_BYTES);
    memset(ecc, 0, sizeof(*ecc));
    nfc_read_calls++;
    return COSMOS_OK;
}

int cosmos_test_nfc_program(const struct cosmos_nfc_io *io) {
    assert(io->data_address == DATA_ADDRESS);
    memcpy(programmed_page, (void *)(uintptr_t)io->data_address,
           sizeof(programmed_page));
    nfc_program_calls++;
    return COSMOS_OK;
}

static enum cosmos_ftl_append_result mock_append(
    void *context, unsigned long long index,
    const struct cosmos_ftl_journal_record *record) {
    (void)context;
    assert(index < 1024ULL);
    assert(record->magic == COSMOS_FTL_MAGIC);
    return COSMOS_FTL_APPEND_COMMITTED;
}

static int cosmos_test_program_data(void *context, unsigned int ppa,
                                    unsigned int lpn,
                                    unsigned long long generation) {
    return cosmos_nvme_ftl_media_program_data(
        context, ppa, lpn, generation);
}

static void put_u32_le(unsigned char *bytes, unsigned int value) {
    unsigned int index;
    for (index = 0U; index < 4U; ++index) {
        bytes[index] = (unsigned char)(value >> (index * 8U));
    }
}

static void put_u64_le(unsigned char *bytes, unsigned long long value) {
    unsigned int index;
    for (index = 0U; index < 8U; ++index) {
        bytes[index] = (unsigned char)(value >> (index * 8U));
    }
}

static struct cosmos_nvme_command command(unsigned int opcode,
                                          unsigned int lba,
                                          unsigned int count) {
    struct cosmos_nvme_command value;

    memset(&value, 0, sizeof(value));
    value.slot_tag = 9U;
    value.namespace_id = COSMOS_NVME_NAMESPACE_ID;
    value.opcode = opcode;
    value.lba_low = lba;
    value.nlb = count == 0U ? 0U : count - 1U;
    value.data_bytes = opcode == COSMOS_NVME_OPCODE_WRITE_ZEROES ? 0U :
        count * COSMOS_FTL_NVME_BLOCK_BYTES;
    return value;
}

int main(void) {
    struct cosmos_ftl_backend backend;
    struct cosmos_ftl ftl;
    struct cosmos_nvme_ftl_media media;
    unsigned int *l2p;
    struct cosmos_ftl_block *blocks;
    unsigned int mapped_ppa;
    unsigned int block_index;
    unsigned int index;
    void *data_map;

    data_map = mmap((void *)(uintptr_t)DATA_ADDRESS, 0x100000U,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    assert(data_map == (void *)(uintptr_t)DATA_ADDRESS);
    assert(mmap((void *)(uintptr_t)SPARE_ADDRESS, 0x1000U,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) ==
           (void *)(uintptr_t)SPARE_ADDRESS);
    assert(mmap((void *)(uintptr_t)COMPLETION_ADDRESS, 0x1000U,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) ==
           (void *)(uintptr_t)COMPLETION_ADDRESS);
    assert(mmap((void *)(uintptr_t)STATUS_ADDRESS, 0x1000U,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) ==
           (void *)(uintptr_t)STATUS_ADDRESS);
    assert(mmap((void *)(uintptr_t)ERROR_ADDRESS, 0x1000U,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) ==
           (void *)(uintptr_t)ERROR_ADDRESS);

    l2p = calloc(8U, sizeof(*l2p));
    blocks = calloc(COSMOS_FTL_BLOCK_COUNT, sizeof(*blocks));
    assert(l2p != 0 && blocks != 0);
    memset(&ftl, 0, sizeof(ftl));
    for (index = 0U; index < 8U; ++index) {
        l2p[index] = COSMOS_FTL_PPA_NONE;
    }
    for (index = 0U; index < COSMOS_FTL_LANE_COUNT; ++index) {
        ftl.open_block[index] = COSMOS_FTL_BLOCK_NONE;
    }
    memset(&backend, 0, sizeof(backend));
    backend.program_data = cosmos_test_program_data;
    backend.append_journal = mock_append;
    backend.journal_capacity = 1024ULL;
    ftl.backend = backend;
    ftl.l2p = l2p;
    ftl.l2p_count = 8U;
    ftl.blocks = blocks;
    ftl.block_count = COSMOS_FTL_BLOCK_COUNT;
    ftl.mounted = 1U;
    assert(cosmos_ftl_ppa_encode(0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN,
                                 0U, &mapped_ppa) == COSMOS_OK);
    {
        unsigned int die;
        unsigned int lun;
        unsigned int page;
        assert(cosmos_ftl_ppa_decode(mapped_ppa, &die, &lun, &block_index,
                                      &page) == COSMOS_OK);
    }
    blocks[block_index].bad = 0U;
    blocks[block_index].state = COSMOS_FTL_BLOCK_OPEN;
    blocks[block_index].valid_pages = 1U;
    l2p[0] = mapped_ppa;

    assert(cosmos_nvme_ftl_media_init(
               &media, &ftl, DATA_ADDRESS, SPARE_ADDRESS,
               COMPLETION_ADDRESS, STATUS_ADDRESS, ERROR_ADDRESS) ==
           COSMOS_OK);
    ftl.backend.context = &media;
    assert(media.media_read == cosmos_nvme_ftl_media_read);
    assert(media.media_program == cosmos_nvme_ftl_media_program);

    memset(host_data, 0xCC, sizeof(host_data));
    {
        struct cosmos_nvme_command read_command =
            command(COSMOS_NVME_OPCODE_READ, 0U, 4U);
        assert(media.media_read(&media, &read_command) == COSMOS_OK);
    }
    assert(nfc_read_calls == 1U && dma_d2h_calls == 4U);
    for (index = 0U; index < 16384U; ++index) {
        assert(host_data[index] == (unsigned char)(0xA0U + (index & 0x0FU)));
    }

    nfc_read_retry_remaining = 2U;
    {
        struct cosmos_nvme_command retry_read =
            command(COSMOS_NVME_OPCODE_READ, 0U, 1U);
        unsigned int attempts = nfc_read_attempts;
        assert(media.media_read(&media, &retry_read) == COSMOS_OK);
        assert(nfc_read_attempts == attempts + 3U);
    }
    nfc_read_retry_remaining = 1U;
    {
        struct cosmos_nvme_command lr_read =
            command(COSMOS_NVME_OPCODE_READ, 0U, 1U);
        unsigned int attempts = nfc_read_attempts;
        lr_read.control = COSMOS_NVME_RW_LR;
        assert(media.media_read(&media, &lr_read) == COSMOS_RETRY);
        assert(nfc_read_attempts == attempts + 1U);
    }

    memset(host_data, 0xCC, sizeof(host_data));
    memset(host_data, 0x3C, 4096U);
    {
        struct cosmos_nvme_command partial_write =
            command(COSMOS_NVME_OPCODE_WRITE, 1U, 1U);
        assert(media.media_program(&media, &partial_write) == COSMOS_OK);
    }
    assert(nfc_read_calls == 2U && nfc_program_calls == 1U);
    assert(programmed_page[0] == 0xA0U && programmed_page[4096U] == 0x3CU);

    memset(host_data, 0x7E, 16384U);
    {
        struct cosmos_nvme_command full_write =
            command(COSMOS_NVME_OPCODE_WRITE, 4U, 4U);
        assert(media.media_program(&media, &full_write) == COSMOS_OK);
    }
    assert(nfc_read_calls == 2U && nfc_program_calls == 2U);
    for (index = 0U; index < 16384U; ++index) {
        assert(programmed_page[index] == 0x7EU);
    }

    {
        struct cosmos_nvme_command zeroes =
            command(COSMOS_NVME_OPCODE_WRITE_ZEROES, 0U, 1U);
        assert(media.media_write_zeroes(&media, &zeroes) == COSMOS_OK);
        assert(nfc_read_calls == 3U && nfc_program_calls == 3U);
        assert(programmed_page[0] == 0U && programmed_page[4096U] == 0xA0U);
    }

    memset(host_data, 0, COSMOS_NVME_DSM_RANGE_BYTES);
    put_u32_le(host_data, 0U);
    put_u32_le(host_data + 4U, 4U);
    put_u64_le(host_data + 8U, 0U);
    {
        struct cosmos_nvme_command dsm = command(
            COSMOS_NVME_OPCODE_DATASET_MANAGEMENT, 0U, 0U);
        dsm.data_bytes = COSMOS_NVME_DSM_RANGE_BYTES;
        dsm.dataset_attributes = COSMOS_NVME_DSM_ATTRIBUTE_DEALLOCATE;
        dsm.dataset_range_count = 1U;
        assert(media.media_deallocate(&media, &dsm) == COSMOS_OK);
        assert(cosmos_ftl_lookup(&ftl, 0U, &mapped_ppa) == COSMOS_UNAVAILABLE);
    }

    free(l2p);
    free(blocks);
    printf("cosmos NVMe FTL media adapter: PASS\n");
    return 0;
}
