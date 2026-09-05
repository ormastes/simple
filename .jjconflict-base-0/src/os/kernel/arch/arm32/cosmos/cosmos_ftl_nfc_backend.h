#ifndef SIMPLE_COSMOS_FTL_NFC_BACKEND_H
#define SIMPLE_COSMOS_FTL_NFC_BACKEND_H

#include "cosmos_ftl.h"
#include "cosmos_nfc_regs.h"

#define COSMOS_FTL_NFC_FORMAT_VERSION 1U
#define COSMOS_FTL_NFC_HEADER_BYTES 36U
#define COSMOS_FTL_NFC_METADATA_PAGE_BYTES COSMOS_NFC_PAGE_DATA_BYTES
#define COSMOS_FTL_NFC_METADATA_PAYLOAD_BYTES \
    (COSMOS_FTL_NFC_METADATA_PAGE_BYTES - COSMOS_FTL_NFC_HEADER_BYTES)
#define COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE \
    (COSMOS_FTL_METADATA_BLOCKS_PER_LUN * COSMOS_FTL_PAGES_PER_BLOCK)
#define COSMOS_FTL_NFC_METADATA_PAGE_COUNT \
    (COSMOS_FTL_LANE_COUNT * COSMOS_FTL_NFC_METADATA_PAGES_PER_LANE)
#define COSMOS_FTL_NFC_JOURNAL_PAGE_BYTES 48U
#define COSMOS_FTL_NFC_CHECKPOINT_BYTES 56U
#define COSMOS_FTL_NFC_DEFAULT_JOURNAL_PAGES 65536U
#define COSMOS_FTL_NFC_MAX_JOURNAL_PAGES 262144U
#define COSMOS_FTL_NFC_MAX_JOURNAL_BLOCKS \
    (COSMOS_FTL_NFC_MAX_JOURNAL_PAGES / COSMOS_FTL_PAGES_PER_BLOCK)

enum cosmos_ftl_nfc_page_type {
    COSMOS_FTL_NFC_PAGE_SUPERBLOCK = 1,
    COSMOS_FTL_NFC_PAGE_CHECKPOINT = 2,
    COSMOS_FTL_NFC_PAGE_CHECKPOINT_DATA = 3,
    COSMOS_FTL_NFC_PAGE_JOURNAL = 4,
    COSMOS_FTL_NFC_PAGE_DATA_TAG = 5
};

struct cosmos_ftl_nfc_dma {
    unsigned int metadata_address;
    unsigned int payload_address;
    unsigned int spare_address;
    unsigned int error_info_address;
    unsigned int completion_address;
    unsigned int status_report_address;
};

struct cosmos_ftl_nfc_ops {
    void *context;
    int (*read_page)(void *context, const struct cosmos_nfc_io *io,
                     struct cosmos_nfc_ecc *ecc);
    int (*program_page)(void *context, const struct cosmos_nfc_io *io);
    int (*erase_block)(void *context, unsigned int channel,
                       unsigned int way, unsigned int row,
                       unsigned int status_report_address);
};

struct cosmos_ftl_nfc_backend {
    struct cosmos_ftl_backend ftl;
    struct cosmos_ftl_nfc_ops nfc;
    struct cosmos_ftl_nfc_dma dma;
    unsigned int l2p_count;
    unsigned int block_count;
    unsigned int checkpoint_data_pages;
    unsigned int checkpoint_record_pages;
    unsigned int checkpoint_slot_pages;
    unsigned int journal_start_page;
    unsigned int journal_blocks;
    unsigned long long checkpoint_payload_bytes;
    unsigned long long journal_capacity;
    unsigned long long journal_first_index;
    unsigned long long journal_next_index;
    unsigned long long checkpoint_generation[2];
    unsigned long long checkpoint_journal_index[2];
    unsigned int checkpoint_valid_mask;
    unsigned int next_checkpoint_segment[2];
    unsigned int mounted;
    unsigned int faulted;
    unsigned char journal_block_erased[COSMOS_FTL_NFC_MAX_JOURNAL_BLOCKS];
};

int cosmos_ftl_nfc_backend_init(
    struct cosmos_ftl_nfc_backend *backend,
    const struct cosmos_ftl_nfc_dma *dma,
    const struct cosmos_ftl_nfc_ops *ops,
    unsigned int l2p_count, unsigned int block_count,
    unsigned long long journal_pages);
int cosmos_ftl_nfc_backend_format(struct cosmos_ftl_nfc_backend *backend);
int cosmos_ftl_nfc_backend_mount(struct cosmos_ftl_nfc_backend *backend);

#endif
