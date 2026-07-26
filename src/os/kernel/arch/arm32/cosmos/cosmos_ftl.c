#include "cosmos_ftl.h"

#define COSMOS_FTL_LUN_BIT 20U
#define COSMOS_FTL_DIE_SHIFT 21U
#define COSMOS_FTL_BLOCK_SHIFT 7U
#define COSMOS_FTL_BLOCK_MASK 0x1FFFU
#define COSMOS_FTL_PAGE_MASK 0x7FU

_Static_assert(sizeof(struct cosmos_ftl_block) == 8U,
               "FTL block format changed");
_Static_assert(sizeof(struct cosmos_ftl_journal_record) == 48U,
               "FTL journal format changed");
_Static_assert(sizeof(struct cosmos_ftl_checkpoint) == 56U,
               "FTL checkpoint format changed");

static unsigned int crc32_step(unsigned int crc, unsigned char byte) {
    unsigned int bit;

    crc ^= byte;
    for (bit = 0U; bit < 8U; ++bit) {
        crc = (crc >> 1U) ^ (0xEDB88320U & (0U - (crc & 1U)));
    }
    return crc;
}

unsigned int cosmos_ftl_crc32(const void *data, unsigned int bytes) {
    const unsigned char *input = data;
    unsigned int crc = 0xFFFFFFFFU;
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        crc = crc32_step(crc, input[index]);
    }
    return ~crc;
}

static unsigned int crc32_u32(unsigned int crc, unsigned int value) {
    unsigned int byte;

    for (byte = 0U; byte < 4U; ++byte) {
        crc = crc32_step(
            crc, (unsigned char)(value >> (byte * 8U)));
    }
    return crc;
}

static unsigned int crc32_u64(
    unsigned int crc, unsigned long long value) {
    unsigned int byte;

    for (byte = 0U; byte < 8U; ++byte) {
        crc = crc32_step(
            crc, (unsigned char)(value >> (byte * 8U)));
    }
    return crc;
}

static unsigned int checkpoint_crc(
    const struct cosmos_ftl_checkpoint *checkpoint) {
    unsigned int crc = 0xFFFFFFFFU;

    crc = crc32_u32(crc, checkpoint->magic);
    crc = crc32_u32(crc, checkpoint->version);
    crc = crc32_u64(crc, checkpoint->generation);
    crc = crc32_u64(crc, checkpoint->journal_index);
    crc = crc32_u32(crc, checkpoint->l2p_count);
    crc = crc32_u32(crc, checkpoint->block_count);
    crc = crc32_u32(crc, checkpoint->allocation_lane);
    crc = crc32_u32(crc, checkpoint->journal_crc);
    crc = crc32_u32(crc, checkpoint->l2p_crc);
    crc = crc32_u32(crc, checkpoint->block_crc);
    return ~crc;
}

unsigned int cosmos_ftl_journal_record_crc(
    const struct cosmos_ftl_journal_record *record) {
    unsigned int crc = 0xFFFFFFFFU;

    crc = crc32_u32(crc, record->magic);
    crc = crc32_u32(crc, record->type);
    crc = crc32_u64(crc, record->sequence);
    crc = crc32_u64(crc, record->generation);
    crc = crc32_u32(crc, record->lpn);
    crc = crc32_u32(crc, record->new_ppa);
    crc = crc32_u32(crc, record->old_ppa);
    crc = crc32_u32(crc, record->block_index);
    crc = crc32_u32(crc, record->previous_crc);
    return ~crc;
}

static unsigned int l2p_crc(const unsigned int *l2p, unsigned int count) {
    unsigned int crc = 0xFFFFFFFFU;
    unsigned int index;
    unsigned int byte;

    for (index = 0U; index < count; ++index) {
        for (byte = 0U; byte < 4U; ++byte) {
            crc = crc32_step(
                crc, (unsigned char)(l2p[index] >> (byte * 8U)));
        }
    }
    return ~crc;
}

static unsigned int blocks_crc(
    const struct cosmos_ftl_block *blocks, unsigned int count) {
    unsigned int crc = 0xFFFFFFFFU;
    unsigned int index;

    for (index = 0U; index < count; ++index) {
        crc = crc32_step(crc, (unsigned char)blocks[index].valid_pages);
        crc = crc32_step(
            crc, (unsigned char)(blocks[index].valid_pages >> 8U));
        crc = crc32_step(crc, (unsigned char)blocks[index].erase_count);
        crc = crc32_step(
            crc, (unsigned char)(blocks[index].erase_count >> 8U));
        crc = crc32_step(crc, blocks[index].bad);
        crc = crc32_step(crc, blocks[index].state);
        crc = crc32_step(crc, blocks[index].next_page);
        crc = crc32_step(crc, blocks[index].reserved);
    }
    return ~crc;
}

int cosmos_ftl_ppa_encode(unsigned int die, unsigned int lun,
                          unsigned int block, unsigned int page,
                          unsigned int *ppa) {
    if (ppa == 0 || die >= COSMOS_FTL_DIE_COUNT ||
        lun >= COSMOS_FTL_LUN_COUNT ||
        block >= COSMOS_FTL_BLOCKS_PER_LUN ||
        page >= COSMOS_FTL_PAGES_PER_BLOCK) {
        return COSMOS_INVALID;
    }
    *ppa = (die << COSMOS_FTL_DIE_SHIFT) |
        (lun << COSMOS_FTL_LUN_BIT) |
        (block << COSMOS_FTL_BLOCK_SHIFT) | page;
    return COSMOS_OK;
}

int cosmos_ftl_ppa_decode(unsigned int ppa, unsigned int *die,
                          unsigned int *lun, unsigned int *block,
                          unsigned int *page) {
    if (die == 0 || lun == 0 || block == 0 || page == 0 ||
        ppa == COSMOS_FTL_PPA_NONE || (ppa >> 27U) != 0U) {
        return COSMOS_INVALID;
    }
    *page = ppa & COSMOS_FTL_PAGE_MASK;
    *block = (ppa >> COSMOS_FTL_BLOCK_SHIFT) & COSMOS_FTL_BLOCK_MASK;
    *lun = (ppa >> COSMOS_FTL_LUN_BIT) & 1U;
    *die = (ppa >> COSMOS_FTL_DIE_SHIFT) & 0x3FU;
    if (*block >= COSMOS_FTL_BLOCKS_PER_LUN) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

int cosmos_ftl_ppa_row(unsigned int ppa, unsigned int *channel,
                       unsigned int *way, unsigned int *row) {
    unsigned int die;
    unsigned int lun;
    unsigned int block;
    unsigned int page;

    if (channel == 0 || way == 0 || row == 0 ||
        cosmos_ftl_ppa_decode(ppa, &die, &lun, &block, &page) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    *channel = die & 7U;
    *way = die >> 3U;
    *row = (lun == 0U ? 0U : 0x00200000U) + block * 256U +
        (page == 0U ? 0U : page * 2U - 1U);
    return COSMOS_OK;
}

static unsigned int block_index_from_parts(unsigned int die, unsigned int lun,
                                            unsigned int block) {
    return (die * COSMOS_FTL_LUN_COUNT + lun) *
        COSMOS_FTL_BLOCKS_PER_LUN + block;
}

static unsigned int lane_index_from_parts(unsigned int die, unsigned int lun) {
    return die * COSMOS_FTL_LUN_COUNT + lun;
}

static void block_parts_from_index(unsigned int index, unsigned int *die,
                                   unsigned int *lun, unsigned int *block) {
    *block = index % COSMOS_FTL_BLOCKS_PER_LUN;
    index /= COSMOS_FTL_BLOCKS_PER_LUN;
    *lun = index % COSMOS_FTL_LUN_COUNT;
    *die = index / COSMOS_FTL_LUN_COUNT;
}

static int block_index_from_ppa(unsigned int ppa, unsigned int *index) {
    unsigned int die;
    unsigned int lun;
    unsigned int block;
    unsigned int page;

    if (index == 0 ||
        cosmos_ftl_ppa_decode(ppa, &die, &lun, &block, &page) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    (void)page;
    *index = block_index_from_parts(die, lun, block);
    return COSMOS_OK;
}

static void clear_tables(struct cosmos_ftl *ftl) {
    unsigned int index;

    for (index = 0U; index < ftl->l2p_count; ++index) {
        ftl->l2p[index] = COSMOS_FTL_PPA_NONE;
    }
    for (index = 0U; index < ftl->block_count; ++index) {
        ftl->blocks[index].valid_pages = 0U;
        ftl->blocks[index].erase_count = 0U;
        ftl->blocks[index].bad = 0U;
        ftl->blocks[index].state = COSMOS_FTL_BLOCK_FREE;
        ftl->blocks[index].next_page = 0U;
        ftl->blocks[index].reserved = 0U;
    }
}

int cosmos_ftl_init(struct cosmos_ftl *ftl,
                    const struct cosmos_ftl_backend *backend,
                    unsigned int *l2p, unsigned int l2p_count,
                    struct cosmos_ftl_block *blocks,
                    unsigned int block_count) {
    if (ftl == 0 || backend == 0 || l2p == 0 || l2p_count == 0U ||
        blocks == 0 || l2p_count > COSMOS_FTL_NAMESPACE_PAGE_COUNT ||
        block_count != COSMOS_FTL_BLOCK_COUNT ||
        backend->program_data == 0 || backend->append_journal == 0 ||
        backend->copy_data == 0 || backend->read_page_tag == 0 ||
        backend->erase_block == 0 || backend->trim_journal == 0 ||
        backend->journal_capacity == 0ULL ||
        backend->read_journal == 0 ||
        backend->read_checkpoint_header == 0 ||
        backend->read_checkpoint_data == 0 ||
        backend->write_checkpoint == 0) {
        return COSMOS_INVALID;
    }
    ftl->backend = *backend;
    ftl->l2p = l2p;
    ftl->l2p_count = l2p_count;
    ftl->blocks = blocks;
    ftl->block_count = block_count;
    ftl->generation = 0ULL;
    ftl->journal_index = 0ULL;
    ftl->journal_first_index = 0ULL;
    ftl->checkpoint_journal_index[0] = 0ULL;
    ftl->checkpoint_journal_index[1] = 0ULL;
    ftl->journal_crc = 0U;
    ftl->active_checkpoint = 0U;
    ftl->checkpoint_valid_mask = 0U;
    ftl->allocation_lane = 0U;
    ftl->mounted = 0U;
    ftl->fail_sticky = 0U;
    return COSMOS_OK;
}

int cosmos_ftl_factory_initialize_erased(struct cosmos_ftl *ftl) {
    return cosmos_ftl_factory_initialize_erased_with_bad_blocks(
        ftl, 0, 0U);
}

int cosmos_ftl_factory_initialize_erased_with_bad_blocks(
    struct cosmos_ftl *ftl, const unsigned char *bad_block_bitmap,
    unsigned int bad_block_bitmap_bytes) {
    unsigned int die;
    unsigned int index;
    unsigned int lun;
    unsigned int block;

    if (ftl == 0) {
        return COSMOS_INVALID;
    }
    if (bad_block_bitmap != 0 &&
        bad_block_bitmap_bytes < (ftl->block_count + 7U) / 8U) {
        return COSMOS_INVALID;
    }
    clear_tables(ftl);
    for (die = 0U; die < COSMOS_FTL_DIE_COUNT; ++die) {
        for (lun = 0U; lun < COSMOS_FTL_LUN_COUNT; ++lun) {
            for (block = 0U; block < COSMOS_FTL_BLOCKS_PER_LUN; ++block) {
                index = block_index_from_parts(die, lun, block);
                if (block < COSMOS_FTL_METADATA_BLOCKS_PER_LUN ||
                    block >= COSMOS_FTL_MAIN_BLOCKS_PER_LUN) {
                    ftl->blocks[index].state = COSMOS_FTL_BLOCK_RESERVED;
                }
            }
        }
    }
    if (bad_block_bitmap != 0) {
        for (index = 0U; index < ftl->block_count; ++index) {
            ftl->blocks[index].bad =
                (bad_block_bitmap[index / 8U] >> (index & 7U)) & 1U;
            if (ftl->blocks[index].bad != 0U) {
                ftl->blocks[index].state = COSMOS_FTL_BLOCK_RETIRED;
            }
        }
    }
    for (index = 0U; index < COSMOS_FTL_LANE_COUNT; ++index) {
        ftl->open_block[index] = COSMOS_FTL_BLOCK_NONE;
    }
    ftl->generation = 0U;
    ftl->journal_index = 0U;
    ftl->journal_first_index = 0U;
    ftl->journal_crc = 0U;
    ftl->active_checkpoint = 1U;
    ftl->checkpoint_journal_index[0] = 0U;
    ftl->checkpoint_journal_index[1] = 0U;
    ftl->checkpoint_valid_mask = 0U;
    ftl->allocation_lane = 0U;
    ftl->mounted = 1U;
    ftl->fail_sticky = 0U;
    return cosmos_ftl_flush(ftl);
}

static int checkpoint_valid(
    const struct cosmos_ftl *ftl,
    const struct cosmos_ftl_checkpoint *checkpoint) {
    return checkpoint->magic == COSMOS_FTL_MAGIC &&
        checkpoint->version == COSMOS_FTL_VERSION &&
        checkpoint->l2p_count == ftl->l2p_count &&
        checkpoint->block_count == ftl->block_count &&
        checkpoint->header_crc == checkpoint_crc(checkpoint);
}

static int load_checkpoint(struct cosmos_ftl *ftl, unsigned int slot,
                           const struct cosmos_ftl_checkpoint *checkpoint) {
    int status = ftl->backend.read_checkpoint_data(
        ftl->backend.context, slot, ftl->l2p, ftl->l2p_count, ftl->blocks,
        ftl->block_count);

    if (status != COSMOS_OK ||
        checkpoint->l2p_crc != l2p_crc(ftl->l2p, ftl->l2p_count) ||
        checkpoint->block_crc != blocks_crc(
            ftl->blocks, ftl->block_count)) {
        return COSMOS_HW_ERROR;
    }
    if (checkpoint->allocation_lane >= COSMOS_FTL_LANE_COUNT) {
        return COSMOS_HW_ERROR;
    }
    ftl->allocation_lane = checkpoint->allocation_lane;
    ftl->generation = checkpoint->generation;
    ftl->journal_index = checkpoint->journal_index;
    ftl->journal_crc = checkpoint->journal_crc;
    ftl->active_checkpoint = slot;
    ftl->checkpoint_journal_index[slot] = checkpoint->journal_index;
    return COSMOS_OK;
}

static void map_apply(struct cosmos_ftl *ftl, unsigned int lpn,
                      unsigned int new_ppa, unsigned int old_ppa) {
    unsigned int block_index;

    if (old_ppa != COSMOS_FTL_PPA_NONE &&
        block_index_from_ppa(old_ppa, &block_index) == COSMOS_OK &&
        ftl->blocks[block_index].valid_pages != 0U) {
        --ftl->blocks[block_index].valid_pages;
    }
    ftl->l2p[lpn] = new_ppa;
    if (block_index_from_ppa(new_ppa, &block_index) == COSMOS_OK) {
        ++ftl->blocks[block_index].valid_pages;
    }
}

static int rebuild_runtime_state(struct cosmos_ftl *ftl) {
    unsigned int die;
    unsigned int index;
    unsigned int lane;
    unsigned int lun;
    unsigned int block;

    for (lane = 0U; lane < COSMOS_FTL_LANE_COUNT; ++lane) {
        ftl->open_block[lane] = COSMOS_FTL_BLOCK_NONE;
    }
    for (index = 0U; index < ftl->block_count; ++index) {
        const struct cosmos_ftl_block *entry = &ftl->blocks[index];

        block_parts_from_index(index, &die, &lun, &block);
        lane = lane_index_from_parts(die, lun);
        if (entry->reserved != 0U ||
            entry->valid_pages > COSMOS_FTL_PAGES_PER_BLOCK ||
            entry->next_page > COSMOS_FTL_PAGES_PER_BLOCK) {
            return COSMOS_HW_ERROR;
        }
        if (block < COSMOS_FTL_METADATA_BLOCKS_PER_LUN ||
            block >= COSMOS_FTL_MAIN_BLOCKS_PER_LUN) {
            if (entry->state != COSMOS_FTL_BLOCK_RESERVED &&
                entry->state != COSMOS_FTL_BLOCK_RETIRED) {
                return COSMOS_HW_ERROR;
            }
            continue;
        }
        if (entry->state == COSMOS_FTL_BLOCK_FREE) {
            if (entry->valid_pages != 0U || entry->next_page != 0U ||
                entry->bad != 0U) {
                return COSMOS_HW_ERROR;
            }
        } else if (entry->state == COSMOS_FTL_BLOCK_OPEN) {
            if (entry->next_page == 0U ||
                entry->next_page >= COSMOS_FTL_PAGES_PER_BLOCK ||
                entry->valid_pages > entry->next_page ||
                entry->bad != 0U ||
                ftl->open_block[lane] != COSMOS_FTL_BLOCK_NONE) {
                return COSMOS_HW_ERROR;
            }
            ftl->open_block[lane] = (unsigned short)block;
        } else if (entry->state == COSMOS_FTL_BLOCK_CLOSED ||
                   entry->state == COSMOS_FTL_BLOCK_EVACUATE) {
            if (entry->next_page == 0U ||
                entry->valid_pages > entry->next_page ||
                entry->bad != 0U) {
                return COSMOS_HW_ERROR;
            }
        } else if (entry->state == COSMOS_FTL_BLOCK_ERASING) {
            if (entry->valid_pages != 0U || entry->bad != 0U) {
                return COSMOS_HW_ERROR;
            }
        } else if (entry->state == COSMOS_FTL_BLOCK_RETIRED) {
            if (entry->bad == 0U || entry->valid_pages != 0U) {
                return COSMOS_HW_ERROR;
            }
        } else {
            return COSMOS_HW_ERROR;
        }
    }
    return COSMOS_OK;
}

static int allocation_ppa_valid(const struct cosmos_ftl *ftl,
                                unsigned int ppa) {
    unsigned int die;
    unsigned int index;
    unsigned int lane;
    unsigned int lun;
    unsigned int block;
    unsigned int page;
    const struct cosmos_ftl_block *entry;

    if (cosmos_ftl_ppa_decode(ppa, &die, &lun, &block, &page) != COSMOS_OK ||
        block < COSMOS_FTL_METADATA_BLOCKS_PER_LUN ||
        block >= COSMOS_FTL_MAIN_BLOCKS_PER_LUN) {
        return 0;
    }
    index = block_index_from_parts(die, lun, block);
    lane = lane_index_from_parts(die, lun);
    entry = &ftl->blocks[index];
    return entry->bad == 0U &&
        ((entry->state == COSMOS_FTL_BLOCK_FREE && page == 0U &&
          ftl->open_block[lane] == COSMOS_FTL_BLOCK_NONE) ||
         (entry->state == COSMOS_FTL_BLOCK_OPEN &&
          ftl->open_block[lane] == block && page == entry->next_page));
}

static void allocation_apply(struct cosmos_ftl *ftl, unsigned int ppa) {
    unsigned int die;
    unsigned int index;
    unsigned int lane;
    unsigned int lun;
    unsigned int block;
    unsigned int page;
    struct cosmos_ftl_block *entry;

    if (cosmos_ftl_ppa_decode(
            ppa, &die, &lun, &block, &page) != COSMOS_OK) {
        return;
    }
    index = block_index_from_parts(die, lun, block);
    lane = lane_index_from_parts(die, lun);
    entry = &ftl->blocks[index];
    if (entry->state == COSMOS_FTL_BLOCK_FREE) {
        entry->state = COSMOS_FTL_BLOCK_OPEN;
        ftl->open_block[lane] = (unsigned short)block;
    }
    entry->next_page = (unsigned char)(page + 1U);
    if (entry->next_page == COSMOS_FTL_PAGES_PER_BLOCK) {
        entry->state = COSMOS_FTL_BLOCK_CLOSED;
        ftl->open_block[lane] = COSMOS_FTL_BLOCK_NONE;
    }
    ftl->allocation_lane = (lane + 1U) % COSMOS_FTL_LANE_COUNT;
}

static void apply_record(struct cosmos_ftl *ftl,
                         const struct cosmos_ftl_journal_record *record) {
    if (record->type == COSMOS_FTL_RECORD_ALLOCATE) {
        allocation_apply(ftl, record->new_ppa);
    } else if (record->type == COSMOS_FTL_RECORD_MAP &&
               record->lpn < ftl->l2p_count) {
        map_apply(ftl, record->lpn, record->new_ppa, record->old_ppa);
        if (record->generation > ftl->generation) {
            ftl->generation = record->generation;
        }
    } else if (record->type == COSMOS_FTL_RECORD_RETIRE &&
               record->block_index < ftl->block_count) {
        ftl->blocks[record->block_index].bad = 1U;
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_RETIRED;
    } else if (record->type == COSMOS_FTL_RECORD_ERASE_BEGIN &&
               record->block_index < ftl->block_count) {
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_ERASING;
    } else if (record->type == COSMOS_FTL_RECORD_ERASE_DONE &&
               record->block_index < ftl->block_count) {
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_FREE;
        ftl->blocks[record->block_index].next_page = 0U;
        if (ftl->blocks[record->block_index].erase_count != 0xFFFFU) {
            ++ftl->blocks[record->block_index].erase_count;
        }
    } else if (record->type == COSMOS_FTL_RECORD_QUARANTINE &&
               record->block_index < ftl->block_count) {
        unsigned int die;
        unsigned int lane;
        unsigned int lun;
        unsigned int block;

        block_parts_from_index(
            record->block_index, &die, &lun, &block);
        lane = lane_index_from_parts(die, lun);
        if (ftl->open_block[lane] == block) {
            ftl->open_block[lane] = COSMOS_FTL_BLOCK_NONE;
        }
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_EVACUATE;
    } else if (record->type == COSMOS_FTL_RECORD_DISCARD &&
               record->lpn < ftl->l2p_count) {
        unsigned int old_block;

        if (block_index_from_ppa(record->old_ppa, &old_block) == COSMOS_OK &&
            ftl->blocks[old_block].valid_pages != 0U) {
            --ftl->blocks[old_block].valid_pages;
        }
        ftl->l2p[record->lpn] = COSMOS_FTL_PPA_NONE;
        ftl->generation = record->generation;
    }
}

static int data_ppa_valid(const struct cosmos_ftl *ftl, unsigned int ppa) {
    unsigned int die;
    unsigned int lun;
    unsigned int block;
    unsigned int page;
    unsigned int index;

    return cosmos_ftl_ppa_decode(
               ppa, &die, &lun, &block, &page) == COSMOS_OK &&
        block >= COSMOS_FTL_METADATA_BLOCKS_PER_LUN &&
        block < COSMOS_FTL_MAIN_BLOCKS_PER_LUN &&
        block_index_from_ppa(ppa, &index) == COSMOS_OK &&
        ftl->blocks[index].bad == 0U;
}

static int append_record(struct cosmos_ftl *ftl, unsigned int type,
                         unsigned long long generation, unsigned int lpn,
                         unsigned int new_ppa, unsigned int old_ppa,
                         unsigned int block_index);

static int journal_has_space(
    const struct cosmos_ftl *ftl, unsigned long long records) {
    return records != 0ULL &&
        records <= ftl->backend.journal_capacity &&
        ftl->journal_index >= ftl->journal_first_index &&
        ftl->journal_index <= ~0ULL - records &&
        ftl->journal_index - ftl->journal_first_index <=
            ftl->backend.journal_capacity - records;
}

int cosmos_ftl_recover(struct cosmos_ftl *ftl) {
    struct cosmos_ftl_checkpoint checkpoint[2];
    unsigned int valid[2] = {0U, 0U};
    unsigned int first;
    unsigned int second;
    unsigned int index;
    unsigned int allocation_pending = 0U;
    unsigned int checkpoint_error = 0U;
    struct cosmos_ftl_journal_record allocation = {0U};

    if (ftl == 0) {
        return COSMOS_INVALID;
    }
    clear_tables(ftl);
    for (index = 0U; index < 2U; ++index) {
        int status = ftl->backend.read_checkpoint_header(
            ftl->backend.context, index, &checkpoint[index]);

        if (status == COSMOS_OK) {
            if (checkpoint_valid(ftl, &checkpoint[index])) {
                valid[index] = 1U;
                ftl->checkpoint_journal_index[index] =
                    checkpoint[index].journal_index;
            } else {
                checkpoint_error = 1U;
            }
        } else if (status != COSMOS_UNAVAILABLE) {
            checkpoint_error = 1U;
        }
    }
    first = valid[1] != 0U &&
        (valid[0] == 0U ||
         checkpoint[1].generation > checkpoint[0].generation ||
         (checkpoint[1].generation == checkpoint[0].generation &&
          checkpoint[1].journal_index >
              checkpoint[0].journal_index)) ? 1U : 0U;
    second = first ^ 1U;
    if (valid[first] != 0U &&
        load_checkpoint(ftl, first, &checkpoint[first]) != COSMOS_OK) {
        valid[first] = 0U;
        checkpoint_error = 1U;
    }
    if (valid[first] == 0U) {
        if (valid[second] == 0U ||
            load_checkpoint(ftl, second, &checkpoint[second]) != COSMOS_OK) {
            ftl->mounted = 0U;
            return checkpoint_error != 0U
                ? COSMOS_HW_ERROR : COSMOS_UNAVAILABLE;
        }
    }
    ftl->checkpoint_valid_mask =
        (valid[0] != 0U ? 1U : 0U) | (valid[1] != 0U ? 2U : 0U);
    ftl->checkpoint_journal_index[0] =
        valid[0] != 0U ? checkpoint[0].journal_index : 0ULL;
    ftl->checkpoint_journal_index[1] =
        valid[1] != 0U ? checkpoint[1].journal_index : 0ULL;
    if (valid[0] != 0U && valid[1] != 0U) {
        ftl->journal_first_index =
            checkpoint[0].journal_index < checkpoint[1].journal_index
                ? checkpoint[0].journal_index
                : checkpoint[1].journal_index;
    } else {
        ftl->journal_first_index =
            checkpoint[valid[0] != 0U ? 0U : 1U].journal_index;
    }
    if (rebuild_runtime_state(ftl) != COSMOS_OK) {
        ftl->mounted = 0U;
        return COSMOS_HW_ERROR;
    }
    for (;;) {
        struct cosmos_ftl_journal_record record;
        int status;

        if (!journal_has_space(ftl, 1ULL)) {
            break;
        }
        status = ftl->backend.read_journal(
            ftl->backend.context, ftl->journal_index, &record);

        if (status == COSMOS_UNAVAILABLE) {
            break;
        }
        if (status == COSMOS_INVALID) {
            ++ftl->journal_index;
            continue;
        }
        if (status != COSMOS_OK || record.magic != COSMOS_FTL_MAGIC ||
            record.sequence != ftl->journal_index ||
            record.previous_crc != ftl->journal_crc ||
            record.crc != cosmos_ftl_journal_record_crc(&record)) {
            ftl->mounted = 0U;
            ftl->fail_sticky = 1U;
            return COSMOS_HW_ERROR;
        }
        if (record.type == COSMOS_FTL_RECORD_ALLOCATE) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation + 1U ||
                record.lpn >= ftl->l2p_count ||
                !data_ppa_valid(ftl, record.new_ppa) ||
                !allocation_ppa_valid(ftl, record.new_ppa) ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index != 0U) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
            allocation = record;
            allocation_pending = 1U;
        } else if (record.type == COSMOS_FTL_RECORD_MAP) {
            if (allocation_pending == 0U ||
                record.generation != allocation.generation ||
                record.lpn != allocation.lpn ||
                record.new_ppa != allocation.new_ppa ||
                record.old_ppa != ftl->l2p[record.lpn] ||
                record.block_index != 0U) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
            allocation_pending = 0U;
        } else if (record.type == COSMOS_FTL_RECORD_RETIRE) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation ||
                record.lpn != 0U ||
                record.new_ppa != COSMOS_FTL_PPA_NONE ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index >= ftl->block_count ||
                ftl->blocks[record.block_index].valid_pages != 0U ||
                (ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_EVACUATE &&
                 ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_FREE &&
                 ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_ERASING)) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
        } else if (record.type == COSMOS_FTL_RECORD_ABANDON) {
            if (allocation_pending == 0U ||
                record.generation != allocation.generation ||
                record.lpn != allocation.lpn ||
                record.new_ppa != allocation.new_ppa ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index != 0U) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
            allocation_pending = 0U;
        } else if (record.type == COSMOS_FTL_RECORD_ERASE_BEGIN) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation ||
                record.lpn != 0U ||
                record.new_ppa != COSMOS_FTL_PPA_NONE ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index >= ftl->block_count ||
                ftl->blocks[record.block_index].valid_pages != 0U ||
                (ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_CLOSED &&
                 ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_EVACUATE)) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
        } else if (record.type == COSMOS_FTL_RECORD_ERASE_DONE) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation ||
                record.lpn != 0U ||
                record.new_ppa != COSMOS_FTL_PPA_NONE ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index >= ftl->block_count ||
                ftl->blocks[record.block_index].state !=
                    COSMOS_FTL_BLOCK_ERASING) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
        } else if (record.type == COSMOS_FTL_RECORD_QUARANTINE) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation ||
                record.lpn != 0U ||
                record.new_ppa != COSMOS_FTL_PPA_NONE ||
                record.old_ppa != COSMOS_FTL_PPA_NONE ||
                record.block_index >= ftl->block_count ||
                (ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_OPEN &&
                 ftl->blocks[record.block_index].state !=
                     COSMOS_FTL_BLOCK_CLOSED)) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
        } else if (record.type == COSMOS_FTL_RECORD_DISCARD) {
            if (allocation_pending != 0U ||
                record.generation != ftl->generation + 1ULL ||
                record.lpn >= ftl->l2p_count ||
                record.new_ppa != COSMOS_FTL_PPA_NONE ||
                record.old_ppa == COSMOS_FTL_PPA_NONE ||
                record.old_ppa != ftl->l2p[record.lpn] ||
                record.block_index != 0U) {
                ftl->mounted = 0U;
                return COSMOS_HW_ERROR;
            }
        } else {
            ftl->mounted = 0U;
            return COSMOS_HW_ERROR;
        }
        apply_record(ftl, &record);
        ftl->journal_crc = record.crc;
        ++ftl->journal_index;
    }
    if (allocation_pending != 0U) {
        if (append_record(
                ftl, COSMOS_FTL_RECORD_ABANDON, allocation.generation,
                allocation.lpn, allocation.new_ppa,
                COSMOS_FTL_PPA_NONE, 0U) != COSMOS_OK) {
            ftl->mounted = 0U;
            ftl->fail_sticky = 1U;
            return COSMOS_HW_ERROR;
        }
    }
    for (index = 0U; index < ftl->block_count; ++index) {
        if (ftl->blocks[index].state == COSMOS_FTL_BLOCK_ERASING) {
            int status = ftl->backend.erase_block(
                ftl->backend.context, index);
            unsigned int record_type = status == COSMOS_OK
                ? COSMOS_FTL_RECORD_ERASE_DONE
                : COSMOS_FTL_RECORD_RETIRE;

            if (append_record(
                    ftl, record_type, ftl->generation,
                    0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE,
                    index) != COSMOS_OK) {
                ftl->mounted = 0U;
                ftl->fail_sticky = 1U;
                return COSMOS_HW_ERROR;
            }
            apply_record(ftl, &(struct cosmos_ftl_journal_record){
                COSMOS_FTL_MAGIC, record_type, 0U,
                ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
                COSMOS_FTL_PPA_NONE, index, 0U, 0U
            });
        }
    }
    ftl->mounted = 1U;
    ftl->fail_sticky = 0U;
    return COSMOS_OK;
}

int cosmos_ftl_lookup(const struct cosmos_ftl *ftl, unsigned int lpn,
                      unsigned int *ppa) {
    unsigned int block_index;

    if (ftl == 0 || ppa == 0 || ftl->mounted == 0U ||
        lpn >= ftl->l2p_count) {
        return COSMOS_INVALID;
    }
    *ppa = ftl->l2p[lpn];
    if (*ppa == COSMOS_FTL_PPA_NONE) {
        return COSMOS_UNAVAILABLE;
    }
    if (block_index_from_ppa(*ppa, &block_index) != COSMOS_OK ||
        ftl->blocks[block_index].bad != 0U) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}

static int append_record(struct cosmos_ftl *ftl, unsigned int type,
                         unsigned long long generation, unsigned int lpn,
                         unsigned int new_ppa, unsigned int old_ppa,
                         unsigned int block_index) {
    struct cosmos_ftl_journal_record record;
    enum cosmos_ftl_append_result result;

    if (ftl->journal_index == ~0ULL ||
        ftl->journal_index - ftl->journal_first_index >=
            ftl->backend.journal_capacity) {
        return COSMOS_UNAVAILABLE;
    }
    record.magic = COSMOS_FTL_MAGIC;
    record.type = type;
    record.sequence = ftl->journal_index;
    record.generation = generation;
    record.lpn = lpn;
    record.new_ppa = new_ppa;
    record.old_ppa = old_ppa;
    record.block_index = block_index;
    record.previous_crc = ftl->journal_crc;
    record.crc = cosmos_ftl_journal_record_crc(&record);
    result = ftl->backend.append_journal(
        ftl->backend.context, ftl->journal_index, &record);
    if (result == COSMOS_FTL_APPEND_COMMITTED) {
        ftl->journal_crc = record.crc;
        ++ftl->journal_index;
        return COSMOS_OK;
    }
    if (result == COSMOS_FTL_APPEND_NOT_COMMITTED) {
        return COSMOS_RETRY;
    }
    ftl->fail_sticky = 1U;
    return result == COSMOS_FTL_APPEND_AMBIGUOUS
        ? COSMOS_COMPLETION_UNCERTAIN : COSMOS_HW_ERROR;
}

static int allocate_page(struct cosmos_ftl *ftl, unsigned int gc,
                         unsigned int excluded_block_index,
                         unsigned int *ppa) {
    unsigned int lane_offset;

    for (lane_offset = 0U; lane_offset < COSMOS_FTL_LANE_COUNT;
         ++lane_offset) {
        unsigned int lane =
            (ftl->allocation_lane + lane_offset) % COSMOS_FTL_LANE_COUNT;
        unsigned int die = lane / COSMOS_FTL_LUN_COUNT;
        unsigned int lun = lane % COSMOS_FTL_LUN_COUNT;
        unsigned int block = ftl->open_block[lane];
        unsigned int free_block = COSMOS_FTL_BLOCK_NONE;
        unsigned int free_count = 0U;

        if (block != COSMOS_FTL_BLOCK_NONE) {
            unsigned int index = block_index_from_parts(die, lun, block);
            struct cosmos_ftl_block *entry = &ftl->blocks[index];

            if (index != excluded_block_index &&
                entry->state == COSMOS_FTL_BLOCK_OPEN &&
                entry->next_page < COSMOS_FTL_PAGES_PER_BLOCK) {
                return cosmos_ftl_ppa_encode(
                    die, lun, block, entry->next_page, ppa);
            }
        }
        for (block = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;
             block < COSMOS_FTL_MAIN_BLOCKS_PER_LUN; ++block) {
            unsigned int index = block_index_from_parts(die, lun, block);

            if (index != excluded_block_index &&
                ftl->blocks[index].state == COSMOS_FTL_BLOCK_FREE &&
                ftl->blocks[index].bad == 0U) {
                if (free_block == COSMOS_FTL_BLOCK_NONE) {
                    free_block = block;
                }
                ++free_count;
            }
        }
        if (free_block != COSMOS_FTL_BLOCK_NONE &&
            ((gc != 0U && free_count != 0U) ||
             free_count > COSMOS_FTL_GC_RESERVE_BLOCKS_PER_LANE)) {
            return cosmos_ftl_ppa_encode(
                die, lun, free_block, 0U, ppa);
        }
    }
    return COSMOS_UNAVAILABLE;
}

static int commit_page_internal(struct cosmos_ftl *ftl, unsigned int lpn,
                                unsigned int source_ppa,
                                unsigned int gc, unsigned int *ppa) {
    unsigned int allocated;
    unsigned int old_ppa;
    unsigned long long generation;
    unsigned int allocated_block;
    unsigned int excluded_block = ~0U;
    int status;

    if (ftl == 0 || ppa == 0 || ftl->mounted == 0U ||
        ftl->fail_sticky != 0U || lpn >= ftl->l2p_count ||
        ftl->generation == ~0ULL) {
        return COSMOS_INVALID;
    }
    if (!journal_has_space(ftl, 3ULL)) {
        return COSMOS_UNAVAILABLE;
    }
    if (source_ppa != COSMOS_FTL_PPA_NONE &&
        block_index_from_ppa(source_ppa, &excluded_block) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    status = allocate_page(ftl, gc, excluded_block, &allocated);
    if (status != COSMOS_OK) {
        return status;
    }
    generation = ftl->generation + 1U;
    status = append_record(
        ftl, COSMOS_FTL_RECORD_ALLOCATE, generation, lpn, allocated,
        COSMOS_FTL_PPA_NONE, 0U);
    if (status != COSMOS_OK) {
        return status;
    }
    allocation_apply(ftl, allocated);
    status = source_ppa == COSMOS_FTL_PPA_NONE
        ? ftl->backend.program_data(
              ftl->backend.context, allocated, lpn, generation)
        : ftl->backend.copy_data(
              ftl->backend.context, source_ppa, allocated, lpn, generation);
    if (status != COSMOS_OK) {
        int abandon = append_record(
            ftl, COSMOS_FTL_RECORD_ABANDON, generation, lpn, allocated,
            COSMOS_FTL_PPA_NONE, 0U);
        if (abandon != COSMOS_OK) {
            ftl->fail_sticky = 1U;
            return abandon;
        }
        if (block_index_from_ppa(allocated, &allocated_block) == COSMOS_OK &&
            ftl->blocks[allocated_block].state !=
                COSMOS_FTL_BLOCK_EVACUATE) {
            int quarantine = append_record(
                ftl, COSMOS_FTL_RECORD_QUARANTINE, ftl->generation,
                0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE,
                allocated_block);

            if (quarantine != COSMOS_OK) {
                ftl->fail_sticky = 1U;
                return quarantine;
            }
            apply_record(ftl, &(struct cosmos_ftl_journal_record){
                COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_QUARANTINE, 0U,
                ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
                COSMOS_FTL_PPA_NONE, allocated_block, 0U, 0U
            });
        }
        return status;
    }
    old_ppa = ftl->l2p[lpn];
    status = append_record(
        ftl, COSMOS_FTL_RECORD_MAP, generation, lpn, allocated, old_ppa, 0U);
    if (status != COSMOS_OK) {
        if (status == COSMOS_RETRY) {
            int abandon = append_record(
                ftl, COSMOS_FTL_RECORD_ABANDON, generation, lpn, allocated,
                COSMOS_FTL_PPA_NONE, 0U);
            if (abandon == COSMOS_OK) {
                return COSMOS_RETRY;
            }
            ftl->fail_sticky = 1U;
            return abandon;
        }
        return status;
    }
    map_apply(ftl, lpn, allocated, old_ppa);
    ftl->generation = generation;
    *ppa = allocated;
    return COSMOS_OK;
}

int cosmos_ftl_commit_page(struct cosmos_ftl *ftl, unsigned int lpn,
                           unsigned int *ppa) {
    return commit_page_internal(
        ftl, lpn, COSMOS_FTL_PPA_NONE, 0U, ppa);
}

int cosmos_ftl_refresh_page(struct cosmos_ftl *ftl, unsigned int lpn,
                            unsigned int source_ppa, unsigned int *ppa) {
    unsigned int mapped;
    int status = cosmos_ftl_lookup(ftl, lpn, &mapped);

    if (status != COSMOS_OK || mapped != source_ppa) {
        return status == COSMOS_OK ? COSMOS_INVALID : status;
    }
    return commit_page_internal(ftl, lpn, source_ppa, 1U, ppa);
}

int cosmos_ftl_discard_page(struct cosmos_ftl *ftl, unsigned int lpn) {
    struct cosmos_ftl_journal_record record;
    unsigned long long generation;
    unsigned int old_ppa;
    int status;

    if (ftl == 0 || ftl->mounted == 0U || ftl->fail_sticky != 0U ||
        lpn >= ftl->l2p_count || ftl->generation == ~0ULL) {
        return COSMOS_INVALID;
    }
    old_ppa = ftl->l2p[lpn];
    if (old_ppa == COSMOS_FTL_PPA_NONE) {
        return COSMOS_OK;
    }
    if (!journal_has_space(ftl, 1ULL)) {
        return COSMOS_UNAVAILABLE;
    }
    generation = ftl->generation + 1ULL;
    status = append_record(
        ftl, COSMOS_FTL_RECORD_DISCARD, generation, lpn,
        COSMOS_FTL_PPA_NONE, old_ppa, 0U);
    if (status != COSMOS_OK) {
        return status;
    }
    record.magic = COSMOS_FTL_MAGIC;
    record.type = COSMOS_FTL_RECORD_DISCARD;
    record.sequence = 0ULL;
    record.generation = generation;
    record.lpn = lpn;
    record.new_ppa = COSMOS_FTL_PPA_NONE;
    record.old_ppa = old_ppa;
    record.block_index = 0U;
    record.previous_crc = 0U;
    record.crc = 0U;
    apply_record(ftl, &record);
    return COSMOS_OK;
}

int cosmos_ftl_retire_block(struct cosmos_ftl *ftl, unsigned int ppa) {
    unsigned int index;
    int status;

    if (ftl == 0 || ftl->mounted == 0U ||
        block_index_from_ppa(ppa, &index) != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    if (ftl->blocks[index].state == COSMOS_FTL_BLOCK_RESERVED ||
        ftl->blocks[index].state == COSMOS_FTL_BLOCK_RETIRED ||
        ftl->blocks[index].state == COSMOS_FTL_BLOCK_ERASING) {
        return COSMOS_INVALID;
    }
    if (!journal_has_space(ftl, 1ULL)) {
        return COSMOS_UNAVAILABLE;
    }
    if (ftl->blocks[index].valid_pages != 0U) {
        if (ftl->blocks[index].state != COSMOS_FTL_BLOCK_EVACUATE) {
            status = append_record(
                ftl, COSMOS_FTL_RECORD_QUARANTINE, ftl->generation,
                0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, index);
            if (status != COSMOS_OK) {
                ftl->fail_sticky = 1U;
                return status;
            }
            apply_record(ftl, &(struct cosmos_ftl_journal_record){
                COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_QUARANTINE, 0U,
                ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
                COSMOS_FTL_PPA_NONE, index, 0U, 0U
            });
        }
        return COSMOS_RETRY;
    }
    if (ftl->blocks[index].state == COSMOS_FTL_BLOCK_OPEN ||
        ftl->blocks[index].state == COSMOS_FTL_BLOCK_CLOSED) {
        status = append_record(
            ftl, COSMOS_FTL_RECORD_QUARANTINE, ftl->generation,
            0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, index);
        if (status != COSMOS_OK) {
            ftl->fail_sticky = 1U;
            return status;
        }
        apply_record(ftl, &(struct cosmos_ftl_journal_record){
            COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_QUARANTINE, 0U,
            ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
            COSMOS_FTL_PPA_NONE, index, 0U, 0U
        });
    }
    status = append_record(
        ftl, COSMOS_FTL_RECORD_RETIRE, ftl->generation,
        0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, index);
    if (status != COSMOS_OK) {
        ftl->fail_sticky = 1U;
        return status;
    }
    ftl->blocks[index].bad = 1U;
    ftl->blocks[index].state = COSMOS_FTL_BLOCK_RETIRED;
    return COSMOS_OK;
}

static int gc_victim(const struct cosmos_ftl *ftl, unsigned int *victim) {
    unsigned int index;
    unsigned int best = ~0U;
    unsigned int best_valid = COSMOS_FTL_PAGES_PER_BLOCK;

    for (index = 0U; index < ftl->block_count; ++index) {
        const struct cosmos_ftl_block *entry = &ftl->blocks[index];

        if (entry->state == COSMOS_FTL_BLOCK_EVACUATE) {
            *victim = index;
            return COSMOS_OK;
        }
        if (entry->state == COSMOS_FTL_BLOCK_CLOSED &&
            entry->valid_pages < COSMOS_FTL_PAGES_PER_BLOCK &&
            (best == ~0U || entry->valid_pages < best_valid ||
             (entry->valid_pages == best_valid &&
              entry->erase_count < ftl->blocks[best].erase_count))) {
            best = index;
            best_valid = entry->valid_pages;
        }
    }
    if (best == ~0U) {
        return COSMOS_UNAVAILABLE;
    }
    *victim = best;
    return COSMOS_OK;
}

static int gc_finish_block(struct cosmos_ftl *ftl, unsigned int victim) {
    int status;

    if (!journal_has_space(
            ftl, ftl->blocks[victim].state ==
                COSMOS_FTL_BLOCK_EVACUATE ? 1ULL : 3ULL)) {
        return COSMOS_UNAVAILABLE;
    }
    if (ftl->blocks[victim].state == COSMOS_FTL_BLOCK_EVACUATE) {
        status = append_record(
            ftl, COSMOS_FTL_RECORD_RETIRE, ftl->generation,
            0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, victim);
        if (status == COSMOS_OK) {
            apply_record(ftl, &(struct cosmos_ftl_journal_record){
                COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_RETIRE, 0U,
                ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
                COSMOS_FTL_PPA_NONE, victim, 0U, 0U
            });
        }
        return status;
    }
    status = append_record(
        ftl, COSMOS_FTL_RECORD_ERASE_BEGIN, ftl->generation,
        0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, victim);
    if (status != COSMOS_OK) {
        return status;
    }
    apply_record(ftl, &(struct cosmos_ftl_journal_record){
        COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_ERASE_BEGIN, 0U,
        ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
        COSMOS_FTL_PPA_NONE, victim, 0U, 0U
    });
    status = ftl->backend.erase_block(ftl->backend.context, victim);
    if (status != COSMOS_OK) {
        int retire = append_record(
            ftl, COSMOS_FTL_RECORD_RETIRE, ftl->generation,
            0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, victim);

        if (retire != COSMOS_OK) {
            ftl->fail_sticky = 1U;
            return retire;
        }
        apply_record(ftl, &(struct cosmos_ftl_journal_record){
            COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_RETIRE, 0U,
            ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
            COSMOS_FTL_PPA_NONE, victim, 0U, 0U
        });
        return status;
    }
    status = append_record(
        ftl, COSMOS_FTL_RECORD_ERASE_DONE, ftl->generation,
        0U, COSMOS_FTL_PPA_NONE, COSMOS_FTL_PPA_NONE, victim);
    if (status != COSMOS_OK) {
        ftl->fail_sticky = 1U;
        return status;
    }
    apply_record(ftl, &(struct cosmos_ftl_journal_record){
        COSMOS_FTL_MAGIC, COSMOS_FTL_RECORD_ERASE_DONE, 0U,
        ftl->generation, 0U, COSMOS_FTL_PPA_NONE,
        COSMOS_FTL_PPA_NONE, victim, 0U, 0U
    });
    return COSMOS_OK;
}

int cosmos_ftl_gc_step(struct cosmos_ftl *ftl, unsigned int max_moves) {
    unsigned int moves = 0U;

    if (ftl == 0 || ftl->mounted == 0U || ftl->fail_sticky != 0U ||
        max_moves == 0U) {
        return COSMOS_INVALID;
    }
    while (moves < max_moves) {
        unsigned int die;
        unsigned int lun;
        unsigned int block;
        unsigned int page;
        unsigned int victim;
        int status = gc_victim(ftl, &victim);

        if (status != COSMOS_OK) {
            return moves != 0U ? COSMOS_OK : status;
        }
        block_parts_from_index(victim, &die, &lun, &block);
        for (page = 0U; page < ftl->blocks[victim].next_page; ++page) {
            unsigned long long generation;
            unsigned int lpn;
            unsigned int destination;
            unsigned int needs_refresh;
            unsigned int source;

            if (cosmos_ftl_ppa_encode(
                    die, lun, block, page, &source) != COSMOS_OK) {
                return COSMOS_HW_ERROR;
            }
            status = ftl->backend.read_page_tag(
                ftl->backend.context, source, &lpn, &generation,
                &needs_refresh);
            if (status == COSMOS_UNAVAILABLE) {
                continue;
            }
            if (status != COSMOS_OK || lpn >= ftl->l2p_count) {
                ftl->fail_sticky = 1U;
                return status != COSMOS_OK ? status : COSMOS_HW_ERROR;
            }
            if (ftl->l2p[lpn] != source) {
                continue;
            }
            (void)generation;
            (void)needs_refresh;
            status = commit_page_internal(
                ftl, lpn, source, 1U, &destination);
            if (status != COSMOS_OK) {
                return status;
            }
            ++moves;
            if (moves == max_moves) {
                return COSMOS_OK;
            }
        }
        if (ftl->blocks[victim].valid_pages != 0U) {
            ftl->fail_sticky = 1U;
            return COSMOS_HW_ERROR;
        }
        status = gc_finish_block(ftl, victim);
        if (status != COSMOS_OK) {
            return status;
        }
        return COSMOS_OK;
    }
    return COSMOS_OK;
}

int cosmos_ftl_flush(struct cosmos_ftl *ftl) {
    struct cosmos_ftl_checkpoint checkpoint;
    unsigned int slot;
    int status;

    if (ftl == 0 || ftl->mounted == 0U || ftl->fail_sticky != 0U) {
        return COSMOS_INVALID;
    }
    checkpoint.magic = COSMOS_FTL_MAGIC;
    checkpoint.version = COSMOS_FTL_VERSION;
    checkpoint.generation = ftl->generation;
    checkpoint.l2p_count = ftl->l2p_count;
    checkpoint.block_count = ftl->block_count;
    checkpoint.allocation_lane = ftl->allocation_lane;
    checkpoint.journal_index = ftl->journal_index;
    checkpoint.journal_crc = ftl->journal_crc;
    checkpoint.l2p_crc = l2p_crc(ftl->l2p, ftl->l2p_count);
    checkpoint.block_crc = blocks_crc(ftl->blocks, ftl->block_count);
    checkpoint.header_crc = checkpoint_crc(&checkpoint);
    slot = ftl->active_checkpoint ^ 1U;
    status = ftl->backend.write_checkpoint(
        ftl->backend.context, slot, ftl->l2p, ftl->l2p_count, ftl->blocks,
        ftl->block_count, &checkpoint);
    if (status == COSMOS_OK) {
        ftl->active_checkpoint = slot;
        ftl->checkpoint_journal_index[slot] = ftl->journal_index;
        ftl->checkpoint_valid_mask |= 1U << slot;
        if (ftl->checkpoint_valid_mask == 3U) {
            unsigned long long first =
                ftl->checkpoint_journal_index[0] <
                    ftl->checkpoint_journal_index[1]
                    ? ftl->checkpoint_journal_index[0]
                    : ftl->checkpoint_journal_index[1];
            int trim_status = ftl->backend.trim_journal(
                ftl->backend.context, first);

            if (trim_status != COSMOS_OK) {
                return trim_status;
            }
            ftl->journal_first_index = first;
        }
    }
    return status;
}
