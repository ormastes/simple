#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "cosmos_nvme_ftl_media.h"

static unsigned char data_dma[COSMOS_NFC_PAGE_DATA_BYTES]
    __attribute__((aligned(COSMOS_NFC_PAGE_DATA_BYTES)));
static unsigned char spare_dma[COSMOS_NFC_PAGE_SPARE_BYTES]
    __attribute__((aligned(COSMOS_NFC_PAGE_SPARE_BYTES)));
static unsigned int completion_dma;
static unsigned int status_dma;
static unsigned int error_dma[COSMOS_NFC_ERROR_INFO_WORDS];
static unsigned int l2p[1U];
static struct cosmos_ftl_block blocks[COSMOS_FTL_BLOCK_COUNT];

int cosmos_test_tag_dma(unsigned int slot, unsigned int offset,
                        unsigned int device_address) {
    (void)slot;
    (void)offset;
    (void)device_address;
    return COSMOS_OK;
}

int cosmos_test_tag_dma_poll(
    enum cosmos_pcie_host_dma_direction direction) {
    (void)direction;
    return COSMOS_OK;
}

int cosmos_test_tag_nfc_read(const struct cosmos_nfc_io *io,
                             struct cosmos_nfc_ecc *ecc) {
    (void)io;
    (void)ecc;
    return COSMOS_OK;
}

int cosmos_test_tag_nfc_program(const struct cosmos_nfc_io *io) {
    (void)io;
    return COSMOS_OK;
}

static int mismatched_tag(void *context, unsigned int ppa,
                          unsigned int *lpn,
                          unsigned long long *generation,
                          unsigned int *needs_refresh) {
    (void)context;
    (void)ppa;
    *lpn = 1U;
    *generation = 1ULL;
    *needs_refresh = 0U;
    return COSMOS_OK;
}

int main(void) {
    struct cosmos_ftl ftl;
    struct cosmos_nvme_ftl_media media;
    struct cosmos_nvme_command command;
    unsigned int ppa;
    unsigned int block_index;

    assert((uintptr_t)data_dma <= UINT32_MAX);
    assert((uintptr_t)spare_dma <= UINT32_MAX);
    assert(cosmos_ftl_ppa_encode(
        0U, 0U, COSMOS_FTL_METADATA_BLOCKS_PER_LUN, 0U, &ppa) == COSMOS_OK);
    block_index = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;
    memset(&ftl, 0, sizeof(ftl));
    l2p[0] = ppa;
    blocks[block_index].state = COSMOS_FTL_BLOCK_OPEN;
    blocks[block_index].valid_pages = 1U;
    ftl.l2p = l2p;
    ftl.l2p_count = 1U;
    ftl.blocks = blocks;
    ftl.block_count = COSMOS_FTL_BLOCK_COUNT;
    ftl.mounted = 1U;
    ftl.backend.read_page_tag = mismatched_tag;
    assert(cosmos_nvme_ftl_media_init(
        &media, &ftl, (unsigned int)(uintptr_t)data_dma,
        (unsigned int)(uintptr_t)spare_dma,
        (unsigned int)(uintptr_t)&completion_dma,
        (unsigned int)(uintptr_t)&status_dma,
        (unsigned int)(uintptr_t)error_dma) == COSMOS_OK);

    memset(&command, 0, sizeof(command));
    command.slot_tag = 1U;
    command.namespace_id = COSMOS_NVME_NAMESPACE_ID;
    command.opcode = COSMOS_NVME_OPCODE_READ;
    command.data_bytes = COSMOS_FTL_NVME_BLOCK_BYTES;
    assert(cosmos_nvme_ftl_media_read(&media, &command) == COSMOS_HW_ERROR);
    puts("cosmos NVMe media page-tag validation: PASS");
    return 0;
}
