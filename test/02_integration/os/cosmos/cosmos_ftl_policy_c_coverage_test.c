/* Independent branch driver for the frozen pre-migration C oracle.
 * Coverage is measured by clang/llvm-cov; this file owns no coverage counters. */
#include <stdint.h>
#include <stdio.h>

#include "cosmos_ftl_policy.h"

static volatile unsigned long long sink;

#define HIT(expr) (sink ^= (unsigned long long)(expr))

static void cover_geometry(void) {
    HIT(cosmos_ftl_policy_crc32_step(0U, 0U));
    HIT(cosmos_ftl_policy_crc32_begin(0U));
    HIT(cosmos_ftl_policy_crc32_begin(1U));
    HIT(cosmos_ftl_policy_crc32_u32(0U, 1U));
    HIT(cosmos_ftl_policy_crc32_u64(0U, 1ULL));
    HIT(cosmos_ftl_policy_checkpoint_crc(1U, 2U, 3ULL, 4ULL, 5U, 6U,
                                          7U, 8U, 9U, 10U));
    HIT(cosmos_ftl_policy_journal_record_crc(1U, 2U, 3ULL, 4ULL, 5U, 6U,
                                              7U, 8U, 9U));
    HIT(cosmos_ftl_policy_l2p_crc_step(0U, 1U));
    HIT(cosmos_ftl_policy_blocks_crc_step(0U, 1U, 2U, 0U, 3U, 4U, 0U));

    HIT(cosmos_ftl_policy_ppa_encode(0U, 0U, 32U, 0U));
    HIT(cosmos_ftl_policy_ppa_encode(64U, 0U, 32U, 0U));
    HIT(cosmos_ftl_policy_ppa_encode(0U, 2U, 32U, 0U));
    HIT(cosmos_ftl_policy_ppa_encode(0U, 0U, 4184U, 0U));
    HIT(cosmos_ftl_policy_ppa_encode(0U, 0U, 32U, 128U));
    HIT(cosmos_ftl_policy_ppa_decode_valid(0U));
    HIT(cosmos_ftl_policy_ppa_decode_valid(0xFFFFFFFFU));
    HIT(cosmos_ftl_policy_ppa_decode_valid(0x08000000U));
    HIT(cosmos_ftl_policy_ppa_decode_valid(4184U << 7U));
    HIT(cosmos_ftl_policy_ppa_row(0xFFFFFFFFU));
    HIT(cosmos_ftl_policy_ppa_row(32U << 7U));
    HIT(cosmos_ftl_policy_ppa_row((1U << 20U) | (32U << 7U) | 1U));
    HIT(cosmos_ftl_policy_block_index_from_parts(1U, 1U, 32U));
    HIT(cosmos_ftl_policy_lane_index_from_parts(1U, 1U));
    HIT(cosmos_ftl_policy_block_parts_from_index(0U));
    HIT(cosmos_ftl_policy_block_parts_from_index(4184U));
    HIT(cosmos_ftl_policy_block_index_from_ppa(0xFFFFFFFFU));
    HIT(cosmos_ftl_policy_block_index_from_ppa(32U << 7U));
    HIT(cosmos_ftl_policy_clear_tables_value(0U));
    HIT(cosmos_ftl_policy_clear_tables_value(1U));
}

static void cover_validation(void) {
    unsigned int i;
    const unsigned int init[][10] = {
        {1U,1U,1U,1U,1U,2U,3U,3U,0x3FFU,1U},
        {0U,1U,1U,1U,1U,2U,3U,3U,0x3FFU,1U},
        {1U,0U,1U,1U,1U,2U,3U,3U,0x3FFU,1U},
        {1U,1U,0U,1U,1U,2U,3U,3U,0x3FFU,1U},
        {1U,1U,1U,0U,1U,2U,3U,3U,0x3FFU,1U},
        {1U,1U,1U,3U,0U,2U,3U,3U,0x3FFU,1U},
        {1U,1U,1U,3U,1U,2U,3U,3U,0x3FFU,1U},
        {1U,1U,1U,1U,1U,2U,2U,3U,0x3FFU,1U},
        {1U,1U,1U,1U,1U,2U,3U,3U,0U,1U},
        {1U,1U,1U,1U,1U,2U,3U,3U,0x3FFU,0U}
    };
    for (i = 0U; i < sizeof(init) / sizeof(init[0]); ++i)
        HIT(cosmos_ftl_policy_init_valid(init[i][0], init[i][1], init[i][2],
            init[i][3], init[i][4], init[i][5], init[i][6], init[i][7],
            init[i][8], init[i][9]));
    HIT(cosmos_ftl_policy_factory_initialize_erased_valid(0U));
    HIT(cosmos_ftl_policy_factory_initialize_erased_valid(1U));
    HIT(cosmos_ftl_policy_factory_block_state(32U, 1U));
    HIT(cosmos_ftl_policy_factory_block_state(0U, 0U));
    HIT(cosmos_ftl_policy_factory_block_state(4096U, 0U));
    HIT(cosmos_ftl_policy_factory_block_state(32U, 0U));

    HIT(cosmos_ftl_policy_checkpoint_valid(0x46544C31U,2U,1U,1U,2U,2U,3U,3U));
    HIT(cosmos_ftl_policy_checkpoint_valid(0U,2U,1U,1U,2U,2U,3U,3U));
    HIT(cosmos_ftl_policy_checkpoint_valid(0x46544C31U,0U,1U,1U,2U,2U,3U,3U));
    HIT(cosmos_ftl_policy_checkpoint_valid(0x46544C31U,2U,0U,1U,2U,2U,3U,3U));
    HIT(cosmos_ftl_policy_checkpoint_valid(0x46544C31U,2U,1U,1U,0U,2U,3U,3U));
    HIT(cosmos_ftl_policy_checkpoint_valid(0x46544C31U,2U,1U,1U,2U,2U,0U,3U));
    HIT(cosmos_ftl_policy_load_checkpoint_status(0U,1U,1U,2U,2U,0U));
    HIT(cosmos_ftl_policy_load_checkpoint_status(4U,1U,1U,2U,2U,0U));
    HIT(cosmos_ftl_policy_load_checkpoint_status(0U,0U,1U,2U,2U,0U));
    HIT(cosmos_ftl_policy_load_checkpoint_status(0U,1U,1U,0U,2U,0U));
    HIT(cosmos_ftl_policy_load_checkpoint_status(0U,1U,1U,2U,2U,128U));

    HIT(cosmos_ftl_policy_map_apply_actions(1U,1U,1U,1U));
    HIT(cosmos_ftl_policy_map_apply_actions(0xFFFFFFFFU,1U,1U,0U));
    HIT(cosmos_ftl_policy_map_apply_actions(1U,0U,1U,0U));
    HIT(cosmos_ftl_policy_map_apply_actions(1U,1U,0U,0U));
}

static void cover_rebuild(void) {
    unsigned int state;
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,0U,0U,0U,1U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,129U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,0U,0U,129U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(0U,0U,0U,1U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(0U,0U,0U,6U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(0U,0U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(4096U,0U,0U,1U,0U,0U,0U));
    for (state = 0U; state <= 7U; ++state) {
        HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,0U,state,0U,0U,0U));
        HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,1U,0U,state,1U,0U,0U));
        HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,1U,1U,state,127U,0U,1U));
        HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,128U,0U,state,127U,0U,1U));
    }
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,1U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,0U,0U,1U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,2U,0U,2U,1U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,1U,0U,2U,128U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,1U,4U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,0U,1U,6U,0U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,1U,0U,2U,127U,0U,0U));
    HIT(cosmos_ftl_policy_rebuild_runtime_state_entry(32U,1U,0U,2U,127U,0U,1U));
}

static void cover_allocation_and_records(void) {
    unsigned int state;
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,0U,0U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(0U,32U,0U,0U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,0U,0U,0U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,4096U,0U,0U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,0U,1U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,1U,0U,0U,0xFFFFU));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,0U,0U,0U,32U));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,1U,0U,2U,32U));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,1U,0U,2U,33U));
    HIT(cosmos_ftl_policy_allocation_ppa_valid(1U,32U,1U,0U,3U,32U));
    HIT(cosmos_ftl_policy_allocation_apply_receipt(0U,0U,32U,0U));
    HIT(cosmos_ftl_policy_allocation_apply_receipt(2U,126U,32U,127U));
    HIT(cosmos_ftl_policy_allocation_apply_receipt(2U,127U,32U,127U));

    for (state = 0U; state <= 9U; ++state) {
        HIT(cosmos_ftl_policy_apply_record_action(state,0U,1U,0U,1U));
        HIT(cosmos_ftl_policy_apply_record_action(state,1U,1U,1U,1U));
    }
    HIT(cosmos_ftl_policy_data_ppa_valid(1U,32U,1U,0U));
    HIT(cosmos_ftl_policy_data_ppa_valid(0U,32U,1U,0U));
    HIT(cosmos_ftl_policy_data_ppa_valid(1U,0U,1U,0U));
    HIT(cosmos_ftl_policy_data_ppa_valid(1U,4096U,1U,0U));
    HIT(cosmos_ftl_policy_data_ppa_valid(1U,32U,0U,0U));
    HIT(cosmos_ftl_policy_data_ppa_valid(1U,32U,1U,1U));
}

static void cover_journal_and_frontend(void) {
    HIT(cosmos_ftl_policy_journal_has_space(3ULL,1ULL,4ULL,1ULL));
    HIT(cosmos_ftl_policy_journal_has_space(3ULL,1ULL,4ULL,0ULL));
    HIT(cosmos_ftl_policy_journal_has_space(3ULL,1ULL,4ULL,5ULL));
    HIT(cosmos_ftl_policy_journal_has_space(0ULL,1ULL,4ULL,1ULL));
    HIT(cosmos_ftl_policy_journal_has_space(UINT64_MAX,0ULL,4ULL,1ULL));
    HIT(cosmos_ftl_policy_journal_has_space(5ULL,0ULL,4ULL,1ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(1U,0U,1ULL,2ULL,3ULL,4ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(0U,1U,1ULL,2ULL,3ULL,4ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(1U,1U,2ULL,1ULL,3ULL,4ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(1U,1U,1ULL,2ULL,3ULL,4ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(1U,1U,2ULL,2ULL,4ULL,3ULL));
    HIT(cosmos_ftl_policy_recover_checkpoint_first(1U,1U,2ULL,2ULL,3ULL,4ULL));

    HIT(cosmos_ftl_policy_lookup_status(1U,1U,1U,0U,1U,1U,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(0U,1U,1U,0U,1U,1U,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,0U,1U,0U,1U,1U,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,1U,0U,0U,1U,1U,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,1U,1U,1U,1U,1U,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,1U,1U,0U,1U,0xFFFFFFFFU,1U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,1U,1U,0U,1U,1U,0U,0U));
    HIT(cosmos_ftl_policy_lookup_status(1U,1U,1U,0U,1U,1U,1U,1U));

    HIT(cosmos_ftl_policy_append_record_result(0ULL,0ULL,1ULL,0U));
    HIT(cosmos_ftl_policy_append_record_result(UINT64_MAX,0ULL,1ULL,0U));
    HIT(cosmos_ftl_policy_append_record_result(0ULL,1ULL,1ULL,0U));
    HIT(cosmos_ftl_policy_append_record_result(1ULL,0ULL,1ULL,0U));
    HIT(cosmos_ftl_policy_append_record_result(0ULL,0ULL,1ULL,1U));
    HIT(cosmos_ftl_policy_append_record_result(0ULL,0ULL,1ULL,2U));
    HIT(cosmos_ftl_policy_append_record_result(0ULL,0ULL,1ULL,3U));
}

static void cover_allocator_boundary(void) {
    HIT(cosmos_ftl_policy_allocate_page_action(1U,1U,0U,0U,0U,0U,410U,0U,1U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,2U,127U,0U,1U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,2U,128U,0U,1U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,1U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,3U,0U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,1U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,0U,0U,0U,1U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,0U,409U,0U,1U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,0U,410U,0U,1U));
    HIT(cosmos_ftl_policy_allocate_page_action(0U,1U,0U,0U,0U,0U,1U,1U,1U));
}

static int allocator_boundary_is_exact(void) {
    return cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 409U, 0U, 1U) == 19U &&
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 410U, 0U, 1U) == 20U &&
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 410U, 0U, 0U) == 19U &&
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 409U, 1U, 1U) == 20U;
}

static void cover_commit_gc(void) {
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,0U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(0U,1U,1U,0U,0U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,0U,1U,0U,0U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,0U,0U,0U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,1U,0U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,1U,1U,0ULL,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,0U,1U,UINT64_MAX,1U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,0U,1U,0ULL,0U,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,0U,1U,0ULL,1U,1U,0U));
    HIT(cosmos_ftl_policy_commit_page_admit(1U,1U,1U,0U,0U,1U,0ULL,1U,1U,1U));
    HIT(cosmos_ftl_policy_commit_page_mode(0xFFFFFFFFU));
    HIT(cosmos_ftl_policy_commit_page_mode(1U));
    HIT(cosmos_ftl_policy_refresh_page_status(1U,1U,1U));
    HIT(cosmos_ftl_policy_refresh_page_status(0U,1U,1U));
    HIT(cosmos_ftl_policy_refresh_page_status(0U,1U,2U));

    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,0U,0U,1U,0ULL,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(0U,1U,0U,0U,1U,0ULL,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,0U,0U,0U,1U,0ULL,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,1U,0U,1U,0ULL,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,0U,1U,1U,0ULL,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,0U,0U,1U,UINT64_MAX,1U,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,0U,0U,1U,0ULL,0xFFFFFFFFU,1U));
    HIT(cosmos_ftl_policy_discard_page_action(1U,1U,0U,0U,1U,0ULL,1U,0U));

    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,0U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(0U,1U,1U,0U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,0U,1U,0U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,0U,0U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,1U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,6U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,4U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,0U,0U,0U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,5U,1U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,3U,1U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,2U,0U,1U));
    HIT(cosmos_ftl_policy_retire_block_action(1U,1U,1U,3U,0U,1U));

    HIT(cosmos_ftl_policy_gc_victim_better(5U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_gc_victim_better(0U,0U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,128U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,1U,0U,0U,2U,1U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,1U,0U,1U,2U,1U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,2U,0U,1U,2U,1U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,2U,0U,1U,2U,0U));
    HIT(cosmos_ftl_policy_gc_victim_better(3U,3U,0U,1U,2U,0U));
    HIT(cosmos_ftl_policy_gc_finish_action(5U,0U));
    HIT(cosmos_ftl_policy_gc_finish_action(5U,1U));
    HIT(cosmos_ftl_policy_gc_finish_action(3U,1U));

    HIT(cosmos_ftl_policy_gc_step_status(1U,1U,0U,1U,0U,0U));
    HIT(cosmos_ftl_policy_gc_step_status(0U,1U,0U,1U,0U,0U));
    HIT(cosmos_ftl_policy_gc_step_status(1U,0U,0U,1U,0U,0U));
    HIT(cosmos_ftl_policy_gc_step_status(1U,1U,1U,1U,0U,0U));
    HIT(cosmos_ftl_policy_gc_step_status(1U,1U,0U,0U,0U,0U));
    HIT(cosmos_ftl_policy_gc_step_status(1U,1U,0U,1U,0U,1U));
    HIT(cosmos_ftl_policy_gc_step_status(1U,1U,0U,1U,1U,1U));
    HIT(cosmos_ftl_policy_flush_action(1U,1U,0U,3U));
    HIT(cosmos_ftl_policy_flush_action(0U,1U,0U,3U));
    HIT(cosmos_ftl_policy_flush_action(1U,0U,0U,3U));
    HIT(cosmos_ftl_policy_flush_action(1U,1U,1U,3U));
    HIT(cosmos_ftl_policy_flush_action(1U,1U,0U,1U));
}

int main(void) {
    cover_geometry();
    cover_validation();
    cover_rebuild();
    cover_allocation_and_records();
    cover_journal_and_frontend();
    cover_allocator_boundary();
    cover_commit_gc();
    if (!allocator_boundary_is_exact()) {
        fputs("cosmos FTL allocator boundary: FAIL\n", stderr);
        return 2;
    }
    puts("cosmos FTL frozen C coverage driver: PASS");
    return sink == UINT64_MAX ? 1 : 0;
}
