#ifndef SIMPLE_COSMOS_FTL_H
#define SIMPLE_COSMOS_FTL_H

#include "cosmos_hal.h"

#define COSMOS_FTL_L2P_BASE 0x18000000U
#define COSMOS_FTL_BLOCK_TABLE_BASE 0x28000000U
#define COSMOS_FTL_DIE_COUNT 64U
#define COSMOS_FTL_LUN_COUNT 2U
#define COSMOS_FTL_BLOCKS_PER_LUN 4184U
#define COSMOS_FTL_MAIN_BLOCKS_PER_LUN 4096U
#define COSMOS_FTL_METADATA_BLOCKS_PER_LUN 32U
#define COSMOS_FTL_PAGES_PER_BLOCK 128U
#define COSMOS_FTL_NVME_BLOCK_BYTES 4096U
#define COSMOS_FTL_NVME_BLOCKS_PER_PAGE 4U
#define COSMOS_FTL_MAIN_BLOCK_COUNT \
    (COSMOS_FTL_MAIN_BLOCKS_PER_LUN * COSMOS_FTL_LUN_COUNT * \
     COSMOS_FTL_DIE_COUNT)
#define COSMOS_FTL_METADATA_BLOCK_COUNT \
    (COSMOS_FTL_METADATA_BLOCKS_PER_LUN * COSMOS_FTL_LUN_COUNT * \
     COSMOS_FTL_DIE_COUNT)
#define COSMOS_FTL_OVERPROVISION_BLOCK_COUNT \
    (COSMOS_FTL_MAIN_BLOCK_COUNT / 10U)
#define COSMOS_FTL_GC_RESERVE_BLOCKS_PER_LANE \
    (COSMOS_FTL_MAIN_BLOCKS_PER_LUN / 10U)
#define COSMOS_FTL_MIN_FREE_BLOCK_COUNT COSMOS_FTL_DIE_COUNT
#define COSMOS_FTL_L2P_ENTRY_COUNT \
    ((COSMOS_FTL_MAIN_BLOCK_COUNT - COSMOS_FTL_METADATA_BLOCK_COUNT) * \
     COSMOS_FTL_PAGES_PER_BLOCK)
#define COSMOS_FTL_NAMESPACE_PAGE_COUNT \
    ((COSMOS_FTL_MAIN_BLOCK_COUNT - COSMOS_FTL_METADATA_BLOCK_COUNT - \
      COSMOS_FTL_OVERPROVISION_BLOCK_COUNT - \
      COSMOS_FTL_MIN_FREE_BLOCK_COUNT) * COSMOS_FTL_PAGES_PER_BLOCK)
#define COSMOS_FTL_NAMESPACE_BLOCK_COUNT \
    (COSMOS_FTL_NAMESPACE_PAGE_COUNT * COSMOS_FTL_NVME_BLOCKS_PER_PAGE)
#define COSMOS_FTL_BLOCK_COUNT \
    (COSMOS_FTL_DIE_COUNT * COSMOS_FTL_LUN_COUNT * \
     COSMOS_FTL_BLOCKS_PER_LUN)
#define COSMOS_FTL_LANE_COUNT \
    (COSMOS_FTL_DIE_COUNT * COSMOS_FTL_LUN_COUNT)
#define COSMOS_FTL_BLOCK_NONE 0xFFFFU
#define COSMOS_FTL_PPA_NONE 0xFFFFFFFFU
#define COSMOS_FTL_MAGIC 0x46544C31U
#define COSMOS_FTL_VERSION 2U

enum cosmos_ftl_record_type {
    COSMOS_FTL_RECORD_ALLOCATE = 1,
    COSMOS_FTL_RECORD_MAP = 2,
    COSMOS_FTL_RECORD_RETIRE = 3,
    COSMOS_FTL_RECORD_ABANDON = 4,
    COSMOS_FTL_RECORD_ERASE_BEGIN = 5,
    COSMOS_FTL_RECORD_ERASE_DONE = 6,
    COSMOS_FTL_RECORD_QUARANTINE = 7,
    COSMOS_FTL_RECORD_DISCARD = 8
};

enum cosmos_ftl_append_result {
    COSMOS_FTL_APPEND_COMMITTED = 0,
    COSMOS_FTL_APPEND_NOT_COMMITTED = 1,
    COSMOS_FTL_APPEND_AMBIGUOUS = 2,
    COSMOS_FTL_APPEND_HARD_FAILED = 3
};

enum cosmos_ftl_block_state {
    COSMOS_FTL_BLOCK_FREE = 0,
    COSMOS_FTL_BLOCK_RESERVED = 1,
    COSMOS_FTL_BLOCK_OPEN = 2,
    COSMOS_FTL_BLOCK_CLOSED = 3,
    COSMOS_FTL_BLOCK_ERASING = 4,
    COSMOS_FTL_BLOCK_EVACUATE = 5,
    COSMOS_FTL_BLOCK_RETIRED = 6
};

struct cosmos_ftl_block {
    unsigned short valid_pages;
    unsigned short erase_count;
    unsigned char bad;
    unsigned char state;
    unsigned char next_page;
    unsigned char reserved;
};

struct cosmos_ftl_journal_record {
    unsigned int magic;
    unsigned int type;
    unsigned long long sequence;
    unsigned long long generation;
    unsigned int lpn;
    unsigned int new_ppa;
    unsigned int old_ppa;
    unsigned int block_index;
    unsigned int previous_crc;
    unsigned int crc;
};

struct cosmos_ftl_checkpoint {
    unsigned int magic;
    unsigned int version;
    unsigned long long generation;
    unsigned long long journal_index;
    unsigned int l2p_count;
    unsigned int block_count;
    unsigned int allocation_lane;
    unsigned int journal_crc;
    unsigned int l2p_crc;
    unsigned int block_crc;
    unsigned int header_crc;
};

struct cosmos_ftl_backend {
    void *context;
    int (*program_data)(void *context, unsigned int ppa, unsigned int lpn,
                        unsigned long long generation);
    int (*copy_data)(void *context, unsigned int source_ppa,
                     unsigned int destination_ppa, unsigned int lpn,
                     unsigned long long generation);
    int (*read_page_tag)(void *context, unsigned int ppa,
                         unsigned int *lpn,
                         unsigned long long *generation,
                         unsigned int *needs_refresh);
    int (*erase_block)(void *context, unsigned int block_index);
    enum cosmos_ftl_append_result (*append_journal)(
        void *context, unsigned long long index,
        const struct cosmos_ftl_journal_record *record);
    int (*read_journal)(
        void *context, unsigned long long index,
        struct cosmos_ftl_journal_record *record);
    int (*trim_journal)(void *context,
                        unsigned long long first_live_index);
    unsigned long long journal_capacity;
    int (*read_checkpoint_header)(
        void *context, unsigned int slot,
        struct cosmos_ftl_checkpoint *checkpoint);
    int (*read_checkpoint_data)(
        void *context, unsigned int slot, unsigned int *l2p,
        unsigned int l2p_count, struct cosmos_ftl_block *blocks,
        unsigned int block_count);
    int (*write_checkpoint)(
        void *context, unsigned int slot, const unsigned int *l2p,
        unsigned int l2p_count, const struct cosmos_ftl_block *blocks,
        unsigned int block_count,
        const struct cosmos_ftl_checkpoint *checkpoint);
};

struct cosmos_ftl {
    struct cosmos_ftl_backend backend;
    unsigned int *l2p;
    unsigned int l2p_count;
    struct cosmos_ftl_block *blocks;
    unsigned int block_count;
    unsigned long long generation;
    unsigned long long journal_index;
    unsigned long long journal_first_index;
    unsigned long long checkpoint_journal_index[2];
    unsigned int journal_crc;
    unsigned int active_checkpoint;
    unsigned int checkpoint_valid_mask;
    unsigned int allocation_lane;
    unsigned int mounted;
    unsigned int fail_sticky;
    unsigned short open_block[COSMOS_FTL_LANE_COUNT];
};

unsigned int cosmos_ftl_crc32(const void *data, unsigned int bytes);
unsigned int cosmos_ftl_journal_record_crc(
    const struct cosmos_ftl_journal_record *record);
int cosmos_ftl_ppa_encode(unsigned int die, unsigned int lun,
                          unsigned int block, unsigned int page,
                          unsigned int *ppa);
int cosmos_ftl_ppa_decode(unsigned int ppa, unsigned int *die,
                          unsigned int *lun, unsigned int *block,
                          unsigned int *page);
int cosmos_ftl_ppa_row(unsigned int ppa, unsigned int *channel,
                       unsigned int *way, unsigned int *row);
int cosmos_ftl_init(struct cosmos_ftl *ftl,
                    const struct cosmos_ftl_backend *backend,
                    unsigned int *l2p, unsigned int l2p_count,
                    struct cosmos_ftl_block *blocks,
                    unsigned int block_count);
int cosmos_ftl_factory_initialize_erased(struct cosmos_ftl *ftl);
int cosmos_ftl_factory_initialize_erased_with_bad_blocks(
    struct cosmos_ftl *ftl, const unsigned char *bad_block_bitmap,
    unsigned int bad_block_bitmap_bytes);
int cosmos_ftl_recover(struct cosmos_ftl *ftl);
int cosmos_ftl_lookup(const struct cosmos_ftl *ftl, unsigned int lpn,
                      unsigned int *ppa);
int cosmos_ftl_commit_page(struct cosmos_ftl *ftl, unsigned int lpn,
                           unsigned int *ppa);
int cosmos_ftl_refresh_page(struct cosmos_ftl *ftl, unsigned int lpn,
                            unsigned int source_ppa, unsigned int *ppa);
int cosmos_ftl_discard_page(struct cosmos_ftl *ftl, unsigned int lpn);
int cosmos_ftl_retire_block(struct cosmos_ftl *ftl, unsigned int ppa);
int cosmos_ftl_gc_step(struct cosmos_ftl *ftl, unsigned int max_moves);
int cosmos_ftl_flush(struct cosmos_ftl *ftl);

#endif
