/* Frozen, independent C oracle for the pre-migration Cosmos FTL policy.
 *
 * This fixture is linked only by host bridge/oracle tests.  Production must
 * resolve the same ABI from cosmos_ftl_policy.spl.  It contains no coverage
 * counters and must not include or call the Simple owner. */
#include <stdint.h>

#include "cosmos_ftl_policy.h"

#define OK 0U
#define UNAVAILABLE 1U
#define INVALID 2U
#define HW_ERROR 4U
#define RETRY 5U
#define COMPLETION_UNCERTAIN 6U
#define DIE_COUNT 64U
#define LUN_COUNT 2U
#define BLOCKS_PER_LUN 4184U
#define MAIN_BLOCKS_PER_LUN 4096U
#define METADATA_BLOCKS_PER_LUN 32U
#define PAGES_PER_BLOCK 128U
#define LANE_COUNT 128U
#define GC_RESERVE 409U
#define BLOCK_NONE 0xFFFFU
#define PPA_NONE 0xFFFFFFFFU
#define MAGIC 0x46544C31U
#define VERSION 2U
#define BLOCK_FREE 0U
#define BLOCK_RESERVED 1U
#define BLOCK_OPEN 2U
#define BLOCK_CLOSED 3U
#define BLOCK_ERASING 4U
#define BLOCK_EVACUATE 5U
#define BLOCK_RETIRED 6U
#define RECORD_ALLOCATE 1U
#define RECORD_MAP 2U
#define RECORD_RETIRE 3U
#define RECORD_ERASE_BEGIN 5U
#define RECORD_ERASE_DONE 6U
#define RECORD_QUARANTINE 7U
#define RECORD_DISCARD 8U
#define ACTION_REJECT 16U
#define ACTION_ACCEPT 17U
#define ACTION_USE_OPEN 18U
#define ACTION_TRACK_FREE 19U
#define ACTION_USE_FREE 20U
#define ACTION_QUARANTINE 21U
#define ACTION_RETIRE 22U
#define ACTION_ERASE 23U

unsigned int cosmos_ftl_policy_crc32_step(unsigned int crc,
                                           unsigned int byte) {
    unsigned int bit;
    crc ^= byte & 0xFFU;
    for (bit = 0U; bit < 8U; ++bit)
        crc = (crc >> 1U) ^ (0xEDB88320U & (0U - (crc & 1U)));
    return crc;
}

unsigned int cosmos_ftl_policy_crc32_begin(unsigned int bytes) {
    return bytes == 0U ? 0U : 0xFFFFFFFFU;
}

unsigned int cosmos_ftl_policy_crc32_u32(unsigned int crc,
                                          unsigned int value) {
    unsigned int byte;
    for (byte = 0U; byte < 4U; ++byte)
        crc = cosmos_ftl_policy_crc32_step(crc, value >> (byte * 8U));
    return crc;
}

unsigned int cosmos_ftl_policy_crc32_u64(unsigned int crc,
                                          unsigned long long value) {
    unsigned int byte;
    for (byte = 0U; byte < 8U; ++byte)
        crc = cosmos_ftl_policy_crc32_step(
            crc, (unsigned int)(value >> (byte * 8U)));
    return crc;
}

unsigned int cosmos_ftl_policy_checkpoint_crc(
    unsigned int magic, unsigned int version, unsigned long long generation,
    unsigned long long journal_index, unsigned int l2p_count,
    unsigned int block_count, unsigned int allocation_lane,
    unsigned int journal_crc, unsigned int l2p_crc, unsigned int block_crc) {
    unsigned int crc = cosmos_ftl_policy_crc32_u32(0xFFFFFFFFU, magic);
    crc = cosmos_ftl_policy_crc32_u32(crc, version);
    crc = cosmos_ftl_policy_crc32_u64(crc, generation);
    crc = cosmos_ftl_policy_crc32_u64(crc, journal_index);
    crc = cosmos_ftl_policy_crc32_u32(crc, l2p_count);
    crc = cosmos_ftl_policy_crc32_u32(crc, block_count);
    crc = cosmos_ftl_policy_crc32_u32(crc, allocation_lane);
    crc = cosmos_ftl_policy_crc32_u32(crc, journal_crc);
    crc = cosmos_ftl_policy_crc32_u32(crc, l2p_crc);
    crc = cosmos_ftl_policy_crc32_u32(crc, block_crc);
    return ~crc;
}

unsigned int cosmos_ftl_policy_journal_record_crc(
    unsigned int magic, unsigned int type, unsigned long long sequence,
    unsigned long long generation, unsigned int lpn, unsigned int new_ppa,
    unsigned int old_ppa, unsigned int block_index,
    unsigned int previous_crc) {
    unsigned int crc = cosmos_ftl_policy_crc32_u32(0xFFFFFFFFU, magic);
    crc = cosmos_ftl_policy_crc32_u32(crc, type);
    crc = cosmos_ftl_policy_crc32_u64(crc, sequence);
    crc = cosmos_ftl_policy_crc32_u64(crc, generation);
    crc = cosmos_ftl_policy_crc32_u32(crc, lpn);
    crc = cosmos_ftl_policy_crc32_u32(crc, new_ppa);
    crc = cosmos_ftl_policy_crc32_u32(crc, old_ppa);
    crc = cosmos_ftl_policy_crc32_u32(crc, block_index);
    crc = cosmos_ftl_policy_crc32_u32(crc, previous_crc);
    return ~crc;
}

unsigned int cosmos_ftl_policy_l2p_crc_step(unsigned int crc,
                                             unsigned int value) {
    return cosmos_ftl_policy_crc32_u32(crc, value);
}

unsigned int cosmos_ftl_policy_blocks_crc_step(
    unsigned int crc, unsigned int valid_pages, unsigned int erase_count,
    unsigned int bad, unsigned int state, unsigned int next_page,
    unsigned int reserved) {
    crc = cosmos_ftl_policy_crc32_step(crc, valid_pages);
    crc = cosmos_ftl_policy_crc32_step(crc, valid_pages >> 8U);
    crc = cosmos_ftl_policy_crc32_step(crc, erase_count);
    crc = cosmos_ftl_policy_crc32_step(crc, erase_count >> 8U);
    crc = cosmos_ftl_policy_crc32_step(crc, bad);
    crc = cosmos_ftl_policy_crc32_step(crc, state);
    crc = cosmos_ftl_policy_crc32_step(crc, next_page);
    return cosmos_ftl_policy_crc32_step(crc, reserved);
}

unsigned long long cosmos_ftl_policy_ppa_encode(
    unsigned int die, unsigned int lun, unsigned int block,
    unsigned int page) {
    if (die >= DIE_COUNT || lun >= LUN_COUNT || block >= BLOCKS_PER_LUN ||
        page >= PAGES_PER_BLOCK) return UINT64_MAX;
    return (unsigned long long)((die << 21U) | (lun << 20U) |
                                (block << 7U) | page);
}

unsigned int cosmos_ftl_policy_ppa_decode_valid(unsigned int ppa) {
    if (ppa == PPA_NONE || (ppa >> 27U) != 0U) return 0U;
    return (((ppa >> 7U) & 0x1FFFU) < BLOCKS_PER_LUN) ? 1U : 0U;
}

unsigned long long cosmos_ftl_policy_ppa_row(unsigned int ppa) {
    unsigned int die, lun, block, page, row;
    if (cosmos_ftl_policy_ppa_decode_valid(ppa) == 0U) return UINT64_MAX;
    die = (ppa >> 21U) & 0x3FU;
    lun = (ppa >> 20U) & 1U;
    block = (ppa >> 7U) & 0x1FFFU;
    page = ppa & 0x7FU;
    row = (lun != 0U ? 0x00200000U : 0U) + block * 256U +
          (page != 0U ? page * 2U - 1U : 0U);
    return (die & 7U) | ((unsigned long long)(die >> 3U) << 8U) |
           ((unsigned long long)row << 16U);
}

unsigned int cosmos_ftl_policy_block_index_from_parts(
    unsigned int die, unsigned int lun, unsigned int block) {
    return (die * LUN_COUNT + lun) * BLOCKS_PER_LUN + block;
}

unsigned int cosmos_ftl_policy_lane_index_from_parts(
    unsigned int die, unsigned int lun) {
    return die * LUN_COUNT + lun;
}

unsigned long long cosmos_ftl_policy_block_parts_from_index(
    unsigned int index) {
    unsigned int block = index % BLOCKS_PER_LUN;
    unsigned int lane = index / BLOCKS_PER_LUN;
    return block | ((unsigned long long)(lane % LUN_COUNT) << 16U) |
           ((unsigned long long)(lane / LUN_COUNT) << 17U);
}

unsigned long long cosmos_ftl_policy_block_index_from_ppa(unsigned int ppa) {
    unsigned int die, lun, block;
    if (cosmos_ftl_policy_ppa_decode_valid(ppa) == 0U) return UINT64_MAX;
    die = (ppa >> 21U) & 0x3FU;
    lun = (ppa >> 20U) & 1U;
    block = (ppa >> 7U) & 0x1FFFU;
    return cosmos_ftl_policy_block_index_from_parts(die, lun, block);
}

unsigned long long cosmos_ftl_policy_clear_tables_value(unsigned int kind) {
    return kind == 0U ? PPA_NONE : BLOCK_FREE;
}

unsigned int cosmos_ftl_policy_init_valid(
    unsigned int ftl_present, unsigned int backend_present,
    unsigned int l2p_present, unsigned int l2p_count,
    unsigned int blocks_present, unsigned int namespace_pages,
    unsigned int block_count, unsigned int expected_blocks,
    unsigned int callback_mask, unsigned long long journal_capacity) {
    return ftl_present != 0U && backend_present != 0U && l2p_present != 0U &&
           l2p_count != 0U && blocks_present != 0U &&
           l2p_count <= namespace_pages && block_count == expected_blocks &&
           callback_mask == 0x3FFU && journal_capacity != 0U ? OK : INVALID;
}

unsigned int cosmos_ftl_policy_factory_initialize_erased_valid(
    unsigned int ftl_present) { return ftl_present != 0U ? OK : INVALID; }

unsigned int cosmos_ftl_policy_factory_block_state(unsigned int block,
                                                     unsigned int bad) {
    if (bad != 0U) return BLOCK_RETIRED | 0x100U;
    if (block < METADATA_BLOCKS_PER_LUN || block >= MAIN_BLOCKS_PER_LUN)
        return BLOCK_RESERVED;
    return BLOCK_FREE;
}

unsigned int cosmos_ftl_policy_checkpoint_valid(
    unsigned int magic, unsigned int version, unsigned int l2p_count,
    unsigned int expected_l2p_count, unsigned int block_count,
    unsigned int expected_block_count, unsigned int header_crc,
    unsigned int expected_header_crc) {
    return magic == MAGIC && version == VERSION &&
           l2p_count == expected_l2p_count &&
           block_count == expected_block_count &&
           header_crc == expected_header_crc;
}

unsigned int cosmos_ftl_policy_load_checkpoint_status(
    unsigned int backend_status, unsigned int l2p_crc,
    unsigned int expected_l2p_crc, unsigned int block_crc,
    unsigned int expected_block_crc, unsigned int allocation_lane) {
    return backend_status == OK && l2p_crc == expected_l2p_crc &&
           block_crc == expected_block_crc && allocation_lane < LANE_COUNT
           ? OK : HW_ERROR;
}

unsigned int cosmos_ftl_policy_map_apply_actions(
    unsigned int old_ppa, unsigned int old_index_valid,
    unsigned int old_valid_pages, unsigned int new_index_valid) {
    unsigned int actions = 0U;
    if (old_ppa != PPA_NONE && old_index_valid != 0U && old_valid_pages != 0U)
        actions |= 1U;
    if (new_index_valid != 0U) actions |= 2U;
    return actions;
}

unsigned int cosmos_ftl_policy_rebuild_runtime_state_entry(
    unsigned int block, unsigned int valid_pages, unsigned int bad,
    unsigned int state, unsigned int next_page, unsigned int reserved,
    unsigned int lane_has_open) {
    if (reserved != 0U || valid_pages > PAGES_PER_BLOCK ||
        next_page > PAGES_PER_BLOCK) return HW_ERROR;
    if (block < METADATA_BLOCKS_PER_LUN || block >= MAIN_BLOCKS_PER_LUN)
        return state == BLOCK_RESERVED || state == BLOCK_RETIRED ? OK : HW_ERROR;
    if (state == BLOCK_FREE)
        return valid_pages == 0U && next_page == 0U && bad == 0U ? OK : HW_ERROR;
    if (state == BLOCK_OPEN)
        return next_page != 0U && next_page < PAGES_PER_BLOCK &&
               valid_pages <= next_page && bad == 0U && lane_has_open == 0U
               ? OK | (ACTION_ACCEPT << 8U) : HW_ERROR;
    if (state == BLOCK_CLOSED || state == BLOCK_EVACUATE)
        return next_page != 0U && valid_pages <= next_page && bad == 0U
               ? OK : HW_ERROR;
    if (state == BLOCK_ERASING)
        return valid_pages == 0U && bad == 0U ? OK : HW_ERROR;
    if (state == BLOCK_RETIRED)
        return bad != 0U && valid_pages == 0U ? OK : HW_ERROR;
    return HW_ERROR;
}

unsigned int cosmos_ftl_policy_allocation_ppa_valid(
    unsigned int ppa_valid, unsigned int block, unsigned int page,
    unsigned int bad, unsigned int state, unsigned int open_block) {
    if (ppa_valid == 0U || block < METADATA_BLOCKS_PER_LUN ||
        block >= MAIN_BLOCKS_PER_LUN || bad != 0U) return 0U;
    if (state == BLOCK_FREE)
        return page == 0U && open_block == BLOCK_NONE;
    if (state == BLOCK_OPEN) return open_block == block;
    return 0U;
}

unsigned long long cosmos_ftl_policy_allocation_apply_receipt(
    unsigned int state, unsigned int page, unsigned int block,
    unsigned int lane) {
    unsigned int next_state = state;
    unsigned int next_page = page + 1U;
    unsigned int next_open = block;
    if (state == BLOCK_FREE) next_state = BLOCK_OPEN;
    if (next_page == PAGES_PER_BLOCK) {
        next_state = BLOCK_CLOSED;
        next_open = BLOCK_NONE;
    }
    return next_state | ((unsigned long long)next_page << 8U) |
           ((unsigned long long)next_open << 16U) |
           ((unsigned long long)((lane + 1U) % LANE_COUNT) << 32U);
}

unsigned int cosmos_ftl_policy_apply_record_action(
    unsigned int type, unsigned int lpn, unsigned int l2p_count,
    unsigned int block_index, unsigned int block_count) {
    if (type == RECORD_ALLOCATE) return type;
    if (type == RECORD_MAP || type == RECORD_DISCARD)
        return lpn < l2p_count ? type : ACTION_REJECT;
    if (type == RECORD_RETIRE || type == RECORD_ERASE_BEGIN ||
        type == RECORD_ERASE_DONE || type == RECORD_QUARANTINE)
        return block_index < block_count ? type : ACTION_REJECT;
    return ACTION_REJECT;
}

unsigned int cosmos_ftl_policy_data_ppa_valid(
    unsigned int ppa_valid, unsigned int block,
    unsigned int block_index_valid, unsigned int bad) {
    return ppa_valid != 0U && block >= METADATA_BLOCKS_PER_LUN &&
           block < MAIN_BLOCKS_PER_LUN && block_index_valid != 0U && bad == 0U;
}

unsigned int cosmos_ftl_policy_journal_has_space(
    unsigned long long journal_index, unsigned long long journal_first_index,
    unsigned long long capacity, unsigned long long records) {
    return records != 0ULL && records <= capacity &&
           journal_index >= journal_first_index &&
           journal_index <= UINT64_MAX - records &&
           journal_index - journal_first_index <= capacity - records;
}

unsigned int cosmos_ftl_policy_recover_checkpoint_first(
    unsigned int valid0, unsigned int valid1,
    unsigned long long generation0, unsigned long long generation1,
    unsigned long long journal0, unsigned long long journal1) {
    return valid1 != 0U && (valid0 == 0U || generation1 > generation0 ||
           (generation1 == generation0 && journal1 > journal0));
}

unsigned int cosmos_ftl_policy_lookup_status(
    unsigned int ftl_present, unsigned int ppa_present, unsigned int mounted,
    unsigned int lpn, unsigned int l2p_count, unsigned int mapped_ppa,
    unsigned int index_valid, unsigned int bad) {
    if (ftl_present == 0U || ppa_present == 0U || mounted == 0U ||
        lpn >= l2p_count) return INVALID;
    if (mapped_ppa == PPA_NONE) return UNAVAILABLE;
    return index_valid != 0U && bad == 0U ? OK : HW_ERROR;
}

unsigned int cosmos_ftl_policy_append_record_result(
    unsigned long long journal_index, unsigned long long journal_first_index,
    unsigned long long capacity, unsigned int append_result) {
    if (journal_index == UINT64_MAX) return UNAVAILABLE;
    if (journal_index < journal_first_index) return HW_ERROR | 0x100U;
    if (journal_index - journal_first_index >= capacity) return UNAVAILABLE;
    if (append_result == 0U) return OK | 0x200U;
    if (append_result == 1U) return RETRY;
    if (append_result == 2U) return COMPLETION_UNCERTAIN | 0x100U;
    return HW_ERROR | 0x100U;
}

unsigned int cosmos_ftl_policy_allocate_page_action(
    unsigned int index, unsigned int excluded_index, unsigned int state,
    unsigned int next_page, unsigned int bad,
    unsigned int is_open_candidate, unsigned int free_count,
    unsigned int gc, unsigned int free_count_is_final) {
    if (index == excluded_index) return ACTION_REJECT;
    if (is_open_candidate != 0U && state == BLOCK_OPEN &&
        next_page < PAGES_PER_BLOCK) return ACTION_USE_OPEN;
    if (state != BLOCK_FREE || bad != 0U) return ACTION_REJECT;
    if (free_count_is_final == 0U || free_count == 0U)
        return ACTION_TRACK_FREE;
    if (gc == 0U && free_count <= GC_RESERVE) return ACTION_TRACK_FREE;
    return ACTION_USE_FREE;
}

unsigned int cosmos_ftl_policy_commit_page_admit(
    unsigned int ftl_present, unsigned int ppa_present, unsigned int mounted,
    unsigned int fail_sticky, unsigned int lpn, unsigned int l2p_count,
    unsigned long long generation, unsigned int journal_space,
    unsigned int source_ppa, unsigned int source_index_valid) {
    if (ftl_present == 0U || ppa_present == 0U || mounted == 0U ||
        fail_sticky != 0U || lpn >= l2p_count || generation == UINT64_MAX)
        return INVALID;
    if (journal_space == 0U) return UNAVAILABLE;
    if (source_ppa != PPA_NONE && source_index_valid == 0U) return INVALID;
    return OK;
}

unsigned int cosmos_ftl_policy_commit_page_mode(unsigned int source_ppa) {
    return source_ppa == PPA_NONE ? 0U : 1U;
}

unsigned int cosmos_ftl_policy_refresh_page_status(
    unsigned int lookup_status, unsigned int mapped_ppa,
    unsigned int source_ppa) {
    if (lookup_status != OK) return lookup_status;
    return mapped_ppa == source_ppa ? OK : INVALID;
}

unsigned int cosmos_ftl_policy_discard_page_action(
    unsigned int ftl_present, unsigned int mounted, unsigned int fail_sticky,
    unsigned int lpn, unsigned int l2p_count,
    unsigned long long generation, unsigned int old_ppa,
    unsigned int journal_space) {
    if (ftl_present == 0U || mounted == 0U || fail_sticky != 0U ||
        lpn >= l2p_count || generation == UINT64_MAX) return INVALID;
    if (old_ppa == PPA_NONE) return OK;
    return journal_space != 0U ? OK | 0x100U : UNAVAILABLE;
}

unsigned int cosmos_ftl_policy_retire_block_action(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int index_valid, unsigned int state,
    unsigned int valid_pages, unsigned int journal_space) {
    if (ftl_present == 0U || mounted == 0U || index_valid == 0U ||
        state == BLOCK_RESERVED || state == BLOCK_RETIRED ||
        state == BLOCK_ERASING) return INVALID;
    if (journal_space == 0U) return UNAVAILABLE;
    if (valid_pages != 0U)
        return state == BLOCK_EVACUATE ? RETRY : ACTION_QUARANTINE;
    if (state == BLOCK_OPEN || state == BLOCK_CLOSED) return ACTION_QUARANTINE;
    return ACTION_RETIRE;
}

unsigned int cosmos_ftl_policy_gc_victim_better(
    unsigned int state, unsigned int valid_pages, unsigned int erase_count,
    unsigned int best_present, unsigned int best_valid,
    unsigned int best_erase_count) {
    if (state == BLOCK_EVACUATE) return 2U;
    if (state != BLOCK_CLOSED || valid_pages >= PAGES_PER_BLOCK) return 0U;
    return best_present == 0U || valid_pages < best_valid ||
           (valid_pages == best_valid && erase_count < best_erase_count);
}

unsigned int cosmos_ftl_policy_gc_finish_action(unsigned int state,
                                                 unsigned int journal_space) {
    if (journal_space == 0U) return UNAVAILABLE;
    return state == BLOCK_EVACUATE ? ACTION_RETIRE : ACTION_ERASE;
}

unsigned int cosmos_ftl_policy_gc_step_status(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int fail_sticky, unsigned int max_moves,
    unsigned int moves, unsigned int victim_status) {
    if (ftl_present == 0U || mounted == 0U || fail_sticky != 0U ||
        max_moves == 0U) return INVALID;
    return victim_status != OK && moves != 0U ? OK : victim_status;
}

unsigned int cosmos_ftl_policy_flush_action(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int fail_sticky,
    unsigned int checkpoint_valid_mask_after_write) {
    if (ftl_present == 0U || mounted == 0U || fail_sticky != 0U)
        return INVALID;
    return checkpoint_valid_mask_after_write == 3U
        ? OK | 0x300U : OK | 0x100U;
}
