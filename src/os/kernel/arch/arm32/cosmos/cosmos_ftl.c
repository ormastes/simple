#include "cosmos_ftl.h"
#include "cosmos_ftl_policy.h"

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
    return cosmos_ftl_policy_crc32_step(crc, byte);
}

unsigned int cosmos_ftl_crc32(const void *data, unsigned int bytes) {
    const unsigned char *input = data;
    unsigned int crc = cosmos_ftl_policy_crc32_begin(bytes);
    unsigned int index;

    for (index = 0U; index < bytes; ++index) {
        crc = crc32_step(crc, input[index]);
    }
    return ~crc;
}

static unsigned int checkpoint_crc(
    const struct cosmos_ftl_checkpoint *checkpoint) {
    return cosmos_ftl_policy_checkpoint_crc(
        checkpoint->magic, checkpoint->version, checkpoint->generation,
        checkpoint->journal_index, checkpoint->l2p_count,
        checkpoint->block_count, checkpoint->allocation_lane,
        checkpoint->journal_crc, checkpoint->l2p_crc, checkpoint->block_crc);
}

unsigned int cosmos_ftl_journal_record_crc(
    const struct cosmos_ftl_journal_record *record) {
    return cosmos_ftl_policy_journal_record_crc(
        record->magic, record->type, record->sequence, record->generation,
        record->lpn, record->new_ppa, record->old_ppa,
        record->block_index, record->previous_crc);
}

static unsigned int l2p_crc(const unsigned int *l2p, unsigned int count) {
    unsigned int crc = 0xFFFFFFFFU;
    unsigned int index;

    for (index = 0U; index < count; ++index) {
        crc = cosmos_ftl_policy_l2p_crc_step(crc, l2p[index]);
    }
    return ~crc;
}

static unsigned int blocks_crc(
    const struct cosmos_ftl_block *blocks, unsigned int count) {
    unsigned int crc = 0xFFFFFFFFU;
    unsigned int index;

    for (index = 0U; index < count; ++index) {
        crc = cosmos_ftl_policy_blocks_crc_step(
            crc, blocks[index].valid_pages, blocks[index].erase_count,
            blocks[index].bad, blocks[index].state,
            blocks[index].next_page, blocks[index].reserved);
    }
    return ~crc;
}

int cosmos_ftl_ppa_encode(unsigned int die, unsigned int lun,
                          unsigned int block, unsigned int page,
                          unsigned int *ppa) {
    unsigned long long receipt;

    if (ppa == 0) {
        return COSMOS_INVALID;
    }
    receipt = cosmos_ftl_policy_ppa_encode(die, lun, block, page);
    if (receipt == ~0ULL) {
        return COSMOS_INVALID;
    }
    *ppa = (unsigned int)receipt;
    return COSMOS_OK;
}

int cosmos_ftl_ppa_decode(unsigned int ppa, unsigned int *die,
                          unsigned int *lun, unsigned int *block,
                          unsigned int *page) {
    if (die == 0 || lun == 0 || block == 0 || page == 0 ||
        cosmos_ftl_policy_ppa_decode_valid(ppa) == 0U) {
        return COSMOS_INVALID;
    }
    *page = ppa & COSMOS_FTL_PAGE_MASK;
    *block = (ppa >> COSMOS_FTL_BLOCK_SHIFT) & COSMOS_FTL_BLOCK_MASK;
    *lun = (ppa >> COSMOS_FTL_LUN_BIT) & 1U;
    *die = (ppa >> COSMOS_FTL_DIE_SHIFT) & 0x3FU;
    return COSMOS_OK;
}

int cosmos_ftl_ppa_row(unsigned int ppa, unsigned int *channel,
                       unsigned int *way, unsigned int *row) {
    unsigned long long receipt;

    if (channel == 0 || way == 0 || row == 0) {
        return COSMOS_INVALID;
    }
    receipt = cosmos_ftl_policy_ppa_row(ppa);
    if (receipt == ~0ULL) {
        return COSMOS_INVALID;
    }
    *channel = (unsigned int)(receipt & 0xFFULL);
    *way = (unsigned int)((receipt >> 8U) & 0xFFULL);
    *row = (unsigned int)(receipt >> 16U);
    return COSMOS_OK;
}

static unsigned int block_index_from_parts(unsigned int die, unsigned int lun,
                                            unsigned int block) {
    return cosmos_ftl_policy_block_index_from_parts(die, lun, block);
}

static unsigned int lane_index_from_parts(unsigned int die, unsigned int lun) {
    return cosmos_ftl_policy_lane_index_from_parts(die, lun);
}

static void block_parts_from_index(unsigned int index, unsigned int *die,
                                   unsigned int *lun, unsigned int *block) {
    unsigned long long receipt =
        cosmos_ftl_policy_block_parts_from_index(index);

    *block = (unsigned int)(receipt & 0xFFFFULL);
    *lun = (unsigned int)((receipt >> 16U) & 1ULL);
    *die = (unsigned int)(receipt >> 17U);
}

static int block_index_from_ppa(unsigned int ppa, unsigned int *index) {
    unsigned long long receipt;

    if (index == 0) {
        return COSMOS_INVALID;
    }
    receipt = cosmos_ftl_policy_block_index_from_ppa(ppa);
    if (receipt == ~0ULL) {
        return COSMOS_INVALID;
    }
    *index = (unsigned int)receipt;
    return COSMOS_OK;
}

static void clear_tables(struct cosmos_ftl *ftl) {
    unsigned int index;

    for (index = 0U; index < ftl->l2p_count; ++index) {
        ftl->l2p[index] =
            (unsigned int)cosmos_ftl_policy_clear_tables_value(0U);
    }
    for (index = 0U; index < ftl->block_count; ++index) {
        ftl->blocks[index].valid_pages = 0U;
        ftl->blocks[index].erase_count = 0U;
        ftl->blocks[index].bad = 0U;
        ftl->blocks[index].state = (unsigned char)
            cosmos_ftl_policy_clear_tables_value(1U);
        ftl->blocks[index].next_page = 0U;
        ftl->blocks[index].reserved = 0U;
    }
}

int cosmos_ftl_init(struct cosmos_ftl *ftl,
                    const struct cosmos_ftl_backend *backend,
                    unsigned int *l2p, unsigned int l2p_count,
                    struct cosmos_ftl_block *blocks,
                    unsigned int block_count) {
    unsigned int callback_mask = 0U;
    unsigned int status;

    if (backend != 0) {
        callback_mask |= backend->program_data != 0 ? 1U : 0U;
        callback_mask |= backend->append_journal != 0 ? 2U : 0U;
        callback_mask |= backend->copy_data != 0 ? 4U : 0U;
        callback_mask |= backend->read_page_tag != 0 ? 8U : 0U;
        callback_mask |= backend->erase_block != 0 ? 16U : 0U;
        callback_mask |= backend->trim_journal != 0 ? 32U : 0U;
        callback_mask |= backend->read_journal != 0 ? 64U : 0U;
        callback_mask |= backend->read_checkpoint_header != 0 ? 128U : 0U;
        callback_mask |= backend->read_checkpoint_data != 0 ? 256U : 0U;
        callback_mask |= backend->write_checkpoint != 0 ? 512U : 0U;
    }
    status = cosmos_ftl_policy_init_valid(
        ftl != 0, backend != 0, l2p != 0, l2p_count, blocks != 0,
        COSMOS_FTL_NAMESPACE_PAGE_COUNT, block_count,
        COSMOS_FTL_BLOCK_COUNT, callback_mask,
        backend != 0 ? backend->journal_capacity : 0ULL);
    if (status != COSMOS_OK) {
        return (int)status;
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
    int status = (int)cosmos_ftl_policy_factory_initialize_erased_valid(
        ftl != 0);

    if (status != COSMOS_OK) {
        return status;
    }
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

    if (cosmos_ftl_policy_factory_initialize_erased_valid(ftl != 0) !=
        COSMOS_OK) {
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
                ftl->blocks[index].state = (unsigned char)
                    cosmos_ftl_policy_factory_block_state(block, 0U);
            }
        }
    }
    if (bad_block_bitmap != 0) {
        for (index = 0U; index < ftl->block_count; ++index) {
            unsigned int bad =
                (bad_block_bitmap[index / 8U] >> (index & 7U)) & 1U;
            unsigned int block_part =
                index % COSMOS_FTL_BLOCKS_PER_LUN;
            unsigned int receipt =
                cosmos_ftl_policy_factory_block_state(block_part, bad);

            ftl->blocks[index].bad = (unsigned char)(receipt >> 8U);
            ftl->blocks[index].state = (unsigned char)receipt;
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
    return (int)cosmos_ftl_policy_checkpoint_valid(
        checkpoint->magic, checkpoint->version, checkpoint->l2p_count,
        ftl->l2p_count, checkpoint->block_count, ftl->block_count,
        checkpoint->header_crc, checkpoint_crc(checkpoint));
}

static int load_checkpoint(struct cosmos_ftl *ftl, unsigned int slot,
                           const struct cosmos_ftl_checkpoint *checkpoint) {
    int status = ftl->backend.read_checkpoint_data(
        ftl->backend.context, slot, ftl->l2p, ftl->l2p_count, ftl->blocks,
        ftl->block_count);

    status = (int)cosmos_ftl_policy_load_checkpoint_status(
        (unsigned int)status, checkpoint->l2p_crc,
        l2p_crc(ftl->l2p, ftl->l2p_count), checkpoint->block_crc,
        blocks_crc(ftl->blocks, ftl->block_count),
        checkpoint->allocation_lane);
    if (status != COSMOS_OK) {
        return status;
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
    unsigned int old_index = 0U;
    unsigned int new_index = 0U;
    unsigned int old_valid = block_index_from_ppa(
        old_ppa, &old_index) == COSMOS_OK;
    unsigned int new_valid = block_index_from_ppa(
        new_ppa, &new_index) == COSMOS_OK;
    unsigned int actions = cosmos_ftl_policy_map_apply_actions(
        old_ppa, old_valid,
        old_valid != 0U ? ftl->blocks[old_index].valid_pages : 0U,
        new_valid);

    if ((actions & 1U) != 0U) {
        --ftl->blocks[old_index].valid_pages;
    }
    ftl->l2p[lpn] = new_ppa;
    if ((actions & 2U) != 0U) {
        ++ftl->blocks[new_index].valid_pages;
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
        unsigned int receipt;

        block_parts_from_index(index, &die, &lun, &block);
        lane = lane_index_from_parts(die, lun);
        receipt = cosmos_ftl_policy_rebuild_runtime_state_entry(
            block, entry->valid_pages, entry->bad, entry->state,
            entry->next_page, entry->reserved,
            ftl->open_block[lane] != COSMOS_FTL_BLOCK_NONE);
        if ((receipt & 0xFFU) != COSMOS_OK) {
            return COSMOS_HW_ERROR;
        }
        if ((receipt >> 8U) != 0U) {
            ftl->open_block[lane] = (unsigned short)block;
        }
    }
    return COSMOS_OK;
}

static int allocation_ppa_valid(const struct cosmos_ftl *ftl,
                                unsigned int ppa) {
    unsigned int die = 0U;
    unsigned int index = 0U;
    unsigned int lane;
    unsigned int lun = 0U;
    unsigned int block = 0U;
    unsigned int page = 0U;
    const struct cosmos_ftl_block *entry;

    unsigned int ppa_valid = cosmos_ftl_ppa_decode(
        ppa, &die, &lun, &block, &page) == COSMOS_OK;

    if (ppa_valid == 0U) {
        return (int)cosmos_ftl_policy_allocation_ppa_valid(
            0U, 0U, 0U, 0U, 0U, COSMOS_FTL_BLOCK_NONE);
    }
    index = block_index_from_parts(die, lun, block);
    lane = lane_index_from_parts(die, lun);
    entry = &ftl->blocks[index];
    if (page != entry->next_page && entry->state == COSMOS_FTL_BLOCK_OPEN) {
        return 0;
    }
    return (int)cosmos_ftl_policy_allocation_ppa_valid(
        ppa_valid, block, page, entry->bad, entry->state,
        ftl->open_block[lane]);
}

static void allocation_apply(struct cosmos_ftl *ftl, unsigned int ppa) {
    unsigned int die;
    unsigned int index;
    unsigned int lane;
    unsigned int lun;
    unsigned int block;
    unsigned int page;
    struct cosmos_ftl_block *entry;
    unsigned long long receipt;

    if (cosmos_ftl_ppa_decode(
            ppa, &die, &lun, &block, &page) != COSMOS_OK) {
        return;
    }
    index = block_index_from_parts(die, lun, block);
    lane = lane_index_from_parts(die, lun);
    entry = &ftl->blocks[index];
    receipt = cosmos_ftl_policy_allocation_apply_receipt(
        entry->state, page, block, lane);
    entry->state = (unsigned char)receipt;
    entry->next_page = (unsigned char)(receipt >> 8U);
    ftl->open_block[lane] = (unsigned short)(receipt >> 16U);
    ftl->allocation_lane = (unsigned int)(receipt >> 32U);
}

static void apply_record(struct cosmos_ftl *ftl,
                         const struct cosmos_ftl_journal_record *record) {
    unsigned int action = cosmos_ftl_policy_apply_record_action(
        record->type, record->lpn, ftl->l2p_count,
        record->block_index, ftl->block_count);

    if (action == COSMOS_FTL_RECORD_ALLOCATE) {
        allocation_apply(ftl, record->new_ppa);
    } else if (action == COSMOS_FTL_RECORD_MAP) {
        map_apply(ftl, record->lpn, record->new_ppa, record->old_ppa);
        if (record->generation > ftl->generation) {
            ftl->generation = record->generation;
        }
    } else if (action == COSMOS_FTL_RECORD_RETIRE) {
        ftl->blocks[record->block_index].bad = 1U;
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_RETIRED;
    } else if (action == COSMOS_FTL_RECORD_ERASE_BEGIN) {
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_ERASING;
    } else if (action == COSMOS_FTL_RECORD_ERASE_DONE) {
        ftl->blocks[record->block_index].state = COSMOS_FTL_BLOCK_FREE;
        ftl->blocks[record->block_index].next_page = 0U;
        if (ftl->blocks[record->block_index].erase_count != 0xFFFFU) {
            ++ftl->blocks[record->block_index].erase_count;
        }
    } else if (action == COSMOS_FTL_RECORD_QUARANTINE) {
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
    } else if (action == COSMOS_FTL_RECORD_DISCARD) {
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
    unsigned int die = 0U;
    unsigned int lun = 0U;
    unsigned int block = 0U;
    unsigned int page = 0U;
    unsigned int index = 0U;

    unsigned int ppa_valid = cosmos_ftl_ppa_decode(
        ppa, &die, &lun, &block, &page) == COSMOS_OK;
    unsigned int index_valid = ppa_valid != 0U &&
        block_index_from_ppa(ppa, &index) == COSMOS_OK;

    (void)die;
    (void)lun;
    (void)page;
    return (int)cosmos_ftl_policy_data_ppa_valid(
        ppa_valid, block, index_valid,
        index_valid != 0U ? ftl->blocks[index].bad : 0U);
}

static int append_record(struct cosmos_ftl *ftl, unsigned int type,
                         unsigned long long generation, unsigned int lpn,
                         unsigned int new_ppa, unsigned int old_ppa,
                         unsigned int block_index);

static int journal_has_space(
    const struct cosmos_ftl *ftl, unsigned long long records) {
    return (int)cosmos_ftl_policy_journal_has_space(
        ftl->journal_index, ftl->journal_first_index,
        ftl->backend.journal_capacity, records);
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
    first = cosmos_ftl_policy_recover_checkpoint_first(
        valid[0], valid[1], checkpoint[0].generation,
        checkpoint[1].generation, checkpoint[0].journal_index,
        checkpoint[1].journal_index);
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
    unsigned int block_index = 0U;
    unsigned int mapped = COSMOS_FTL_PPA_NONE;
    unsigned int index_valid = 0U;
    unsigned int bad = 0U;
    unsigned int status;

    if (ftl != 0 && lpn < ftl->l2p_count) {
        mapped = ftl->l2p[lpn];
        index_valid = block_index_from_ppa(mapped, &block_index) == COSMOS_OK;
        if (index_valid != 0U) {
            bad = ftl->blocks[block_index].bad;
        }
    }
    status = cosmos_ftl_policy_lookup_status(
        ftl != 0, ppa != 0, ftl != 0 ? ftl->mounted : 0U,
        lpn, ftl != 0 ? ftl->l2p_count : 0U, mapped, index_valid, bad);
    if (status == COSMOS_OK || status == COSMOS_UNAVAILABLE) {
        *ppa = mapped;
    }
    return (int)status;
}

static int append_record(struct cosmos_ftl *ftl, unsigned int type,
                         unsigned long long generation, unsigned int lpn,
                         unsigned int new_ppa, unsigned int old_ppa,
                         unsigned int block_index) {
    struct cosmos_ftl_journal_record record;
    enum cosmos_ftl_append_result result;

    unsigned int action = cosmos_ftl_policy_append_record_result(
        ftl->journal_index, ftl->journal_first_index,
        ftl->backend.journal_capacity, COSMOS_FTL_APPEND_COMMITTED);

    if ((action & 0xFFU) != COSMOS_OK) {
        return (int)(action & 0xFFU);
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
    action = cosmos_ftl_policy_append_record_result(
        ftl->journal_index, ftl->journal_first_index,
        ftl->backend.journal_capacity, result);
    if ((action & 0x200U) != 0U) {
        ftl->journal_crc = record.crc;
        ++ftl->journal_index;
        return COSMOS_OK;
    }
    if ((action & 0x100U) != 0U) {
        ftl->fail_sticky = 1U;
    }
    return (int)(action & 0xFFU);
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
            unsigned int action = cosmos_ftl_policy_allocate_page_action(
                index, excluded_block_index, entry->state,
                entry->next_page, entry->bad, 1U, 0U, gc, 0U);

            if (action == 18U) {
                return cosmos_ftl_ppa_encode(
                    die, lun, block, entry->next_page, ppa);
            }
        }
        for (block = COSMOS_FTL_METADATA_BLOCKS_PER_LUN;
             block < COSMOS_FTL_MAIN_BLOCKS_PER_LUN; ++block) {
            unsigned int index = block_index_from_parts(die, lun, block);
            unsigned int action = cosmos_ftl_policy_allocate_page_action(
                index, excluded_block_index, ftl->blocks[index].state,
                ftl->blocks[index].next_page, ftl->blocks[index].bad,
                0U, free_count, gc, 0U);

            if (action == 19U || action == 20U) {
                if (free_block == COSMOS_FTL_BLOCK_NONE) {
                    free_block = block;
                }
                ++free_count;
            }
        }
        if (free_block != COSMOS_FTL_BLOCK_NONE &&
            cosmos_ftl_policy_allocate_page_action(
                0U, ~0U, COSMOS_FTL_BLOCK_FREE, 0U, 0U, 0U,
                free_count, gc, 1U) == 20U) {
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
    unsigned int excluded_block = ~0U;
    unsigned int source_index_valid = 1U;
    unsigned int admit;
    int status;

    if (source_ppa != COSMOS_FTL_PPA_NONE) {
        source_index_valid = ftl != 0 &&
            block_index_from_ppa(source_ppa, &excluded_block) == COSMOS_OK;
    }
    admit = cosmos_ftl_policy_commit_page_admit(
        ftl != 0, ppa != 0, ftl != 0 ? ftl->mounted : 0U,
        ftl != 0 ? ftl->fail_sticky : 0U, lpn,
        ftl != 0 ? ftl->l2p_count : 0U,
        ftl != 0 ? ftl->generation : 0ULL,
        ftl != 0 ? (unsigned int)journal_has_space(ftl, 3ULL) : 0U,
        source_ppa, source_index_valid);
    if (admit != COSMOS_OK) {
        return (int)admit;
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
    status = cosmos_ftl_policy_commit_page_mode(source_ppa) == 0U
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
    (void)cosmos_ftl_policy_commit_page_mode(COSMOS_FTL_PPA_NONE);
    return commit_page_internal(
        ftl, lpn, COSMOS_FTL_PPA_NONE, 0U, ppa);
}

int cosmos_ftl_refresh_page(struct cosmos_ftl *ftl, unsigned int lpn,
                            unsigned int source_ppa, unsigned int *ppa) {
    unsigned int mapped;
    int status = cosmos_ftl_lookup(ftl, lpn, &mapped);

    status = (int)cosmos_ftl_policy_refresh_page_status(
        (unsigned int)status, mapped, source_ppa);
    if (status != COSMOS_OK) {
        return status;
    }
    return commit_page_internal(ftl, lpn, source_ppa, 1U, ppa);
}

int cosmos_ftl_discard_page(struct cosmos_ftl *ftl, unsigned int lpn) {
    struct cosmos_ftl_journal_record record;
    unsigned long long generation;
    unsigned int old_ppa;
    unsigned int action;
    int status;

    old_ppa = ftl != 0 && lpn < ftl->l2p_count
        ? ftl->l2p[lpn] : COSMOS_FTL_PPA_NONE;
    action = cosmos_ftl_policy_discard_page_action(
        ftl != 0, ftl != 0 ? ftl->mounted : 0U,
        ftl != 0 ? ftl->fail_sticky : 0U, lpn,
        ftl != 0 ? ftl->l2p_count : 0U,
        ftl != 0 ? ftl->generation : 0ULL, old_ppa,
        ftl != 0 ? (unsigned int)journal_has_space(ftl, 1ULL) : 0U);
    if ((action & 0x100U) == 0U) {
        return (int)(action & 0xFFU);
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
    unsigned int index = 0U;
    unsigned int index_valid = ftl != 0 &&
        block_index_from_ppa(ppa, &index) == COSMOS_OK;
    unsigned int action = cosmos_ftl_policy_retire_block_action(
        ftl != 0, ftl != 0 ? ftl->mounted : 0U, index_valid,
        index_valid != 0U ? ftl->blocks[index].state : 0U,
        index_valid != 0U ? ftl->blocks[index].valid_pages : 0U,
        ftl != 0 ? (unsigned int)journal_has_space(ftl, 1ULL) : 0U);
    int status;

    if (action <= COSMOS_COMPLETION_UNCERTAIN) {
        return (int)action;
    }
    if (action == 21U) {
        if (ftl->blocks[index].valid_pages != 0U ||
            ftl->blocks[index].state != COSMOS_FTL_BLOCK_EVACUATE) {
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
        if (ftl->blocks[index].valid_pages != 0U) {
            return COSMOS_RETRY;
        }
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
        unsigned int choice = cosmos_ftl_policy_gc_victim_better(
            entry->state, entry->valid_pages, entry->erase_count,
            best != ~0U, best_valid,
            best != ~0U ? ftl->blocks[best].erase_count : 0U);

        if (choice == 2U) {
            *victim = index;
            return COSMOS_OK;
        }
        if (choice == 1U) {
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
    unsigned int action = cosmos_ftl_policy_gc_finish_action(
        ftl->blocks[victim].state,
        (unsigned int)journal_has_space(
            ftl, ftl->blocks[victim].state ==
                COSMOS_FTL_BLOCK_EVACUATE ? 1ULL : 3ULL));
    int status;

    if (action == COSMOS_UNAVAILABLE) {
        return (int)action;
    }
    if (action == 22U) {
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
    unsigned int admit = cosmos_ftl_policy_gc_step_status(
        ftl != 0, ftl != 0 ? ftl->mounted : 0U,
        ftl != 0 ? ftl->fail_sticky : 0U, max_moves, 0U, COSMOS_OK);

    if (admit != COSMOS_OK) {
        return (int)admit;
    }
    while (moves < max_moves) {
        unsigned int die;
        unsigned int lun;
        unsigned int block;
        unsigned int page;
        unsigned int victim;
        int status = gc_victim(ftl, &victim);

        if (status != COSMOS_OK) {
            return (int)cosmos_ftl_policy_gc_step_status(
                1U, ftl->mounted, ftl->fail_sticky,
                max_moves, moves, (unsigned int)status);
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
    unsigned int action = cosmos_ftl_policy_flush_action(
        ftl != 0, ftl != 0 ? ftl->mounted : 0U,
        ftl != 0 ? ftl->fail_sticky : 0U,
        ftl != 0 ? ftl->checkpoint_valid_mask : 0U);
    int status;

    if ((action & 0xFFU) != COSMOS_OK) {
        return (int)(action & 0xFFU);
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
        action = cosmos_ftl_policy_flush_action(
            1U, ftl->mounted, ftl->fail_sticky,
            ftl->checkpoint_valid_mask);
        if ((action & 0x200U) != 0U) {
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
