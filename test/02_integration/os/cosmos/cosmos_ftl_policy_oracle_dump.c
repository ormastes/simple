#include <inttypes.h>
#include <stdio.h>

#include "cosmos_ftl_policy.h"

static void emit(unsigned int id, unsigned long long value) {
    printf("FTL|%u|%" PRIu64 "\n", id, (uint64_t)value);
}

int main(void) {
    emit(1U, cosmos_ftl_policy_crc32_step(0xFFFFFFFFU, 0x5AU));
    emit(2U, cosmos_ftl_policy_crc32_begin(4U));
    emit(3U, cosmos_ftl_policy_crc32_u32(0xFFFFFFFFU, 0x12345678U));
    emit(4U, cosmos_ftl_policy_crc32_u64(
        0xFFFFFFFFU, UINT64_C(0x0123456789abcdef)));
    emit(5U, cosmos_ftl_policy_checkpoint_crc(
        0x46544C31U, 2U, 3ULL, 4ULL, 5U, 6U, 7U, 8U, 9U, 10U));
    emit(6U, cosmos_ftl_policy_journal_record_crc(
        0x46544C31U, 2U, 3ULL, 4ULL, 5U, 6U, 7U, 8U, 9U));
    emit(7U, cosmos_ftl_policy_l2p_crc_step(1U, 2U));
    emit(8U, cosmos_ftl_policy_blocks_crc_step(1U, 2U, 3U, 0U, 2U, 4U, 0U));
    emit(9U, cosmos_ftl_policy_ppa_encode(63U, 1U, 4183U, 127U));
    emit(10U, cosmos_ftl_policy_ppa_decode_valid(0x07FFFFFFU));
    emit(11U, cosmos_ftl_policy_ppa_row(0x00100001U));
    emit(12U, cosmos_ftl_policy_block_index_from_parts(3U, 1U, 32U));
    emit(13U, cosmos_ftl_policy_lane_index_from_parts(3U, 1U));
    emit(14U, cosmos_ftl_policy_block_parts_from_index(4184U));
    emit(15U, cosmos_ftl_policy_block_index_from_ppa(0x00100000U));
    emit(16U, cosmos_ftl_policy_clear_tables_value(0U));
    emit(17U, cosmos_ftl_policy_init_valid(
        1U, 1U, 1U, 1U, 1U, 2U, 3U, 3U, 0x3FFU, 1ULL));
    emit(18U, cosmos_ftl_policy_factory_initialize_erased_valid(1U));
    emit(19U, cosmos_ftl_policy_factory_block_state(32U, 0U));
    emit(20U, cosmos_ftl_policy_checkpoint_valid(
        0x46544C31U, 2U, 1U, 1U, 2U, 2U, 3U, 3U));
    emit(21U, cosmos_ftl_policy_load_checkpoint_status(
        0U, 1U, 1U, 2U, 2U, 0U));
    emit(22U, cosmos_ftl_policy_map_apply_actions(1U, 1U, 1U, 1U));
    emit(23U, cosmos_ftl_policy_rebuild_runtime_state_entry(
        32U, 1U, 0U, 2U, 1U, 0U, 0U));
    emit(24U, cosmos_ftl_policy_allocation_ppa_valid(
        1U, 32U, 0U, 0U, 0U, 0xFFFFU));
    emit(25U, cosmos_ftl_policy_allocation_apply_receipt(0U, 0U, 32U, 0U));
    emit(26U, cosmos_ftl_policy_apply_record_action(2U, 0U, 1U, 0U, 1U));
    emit(27U, cosmos_ftl_policy_data_ppa_valid(1U, 32U, 1U, 0U));
    emit(28U, cosmos_ftl_policy_journal_has_space(1ULL, 0ULL, 4ULL, 1ULL));
    emit(29U, cosmos_ftl_policy_recover_checkpoint_first(
        1U, 1U, 1ULL, 2ULL, 3ULL, 4ULL));
    emit(30U, cosmos_ftl_policy_lookup_status(
        1U, 1U, 1U, 0U, 1U, 2U, 1U, 0U));
    emit(31U, cosmos_ftl_policy_append_record_result(0ULL, 0ULL, 4ULL, 0U));
    emit(32U, cosmos_ftl_policy_allocate_page_action(
        0U, ~0U, 0U, 0U, 0U, 0U, 409U, 0U, 1U));
    emit(33U, cosmos_ftl_policy_commit_page_admit(
        1U, 1U, 1U, 0U, 0U, 1U, 0ULL, 1U, 0xFFFFFFFFU, 1U));
    emit(34U, cosmos_ftl_policy_commit_page_mode(0xFFFFFFFFU));
    emit(35U, cosmos_ftl_policy_refresh_page_status(0U, 1U, 1U));
    emit(36U, cosmos_ftl_policy_discard_page_action(
        1U, 1U, 0U, 0U, 1U, 0ULL, 1U, 1U));
    emit(37U, cosmos_ftl_policy_retire_block_action(1U, 1U, 1U, 3U, 0U, 1U));
    emit(38U, cosmos_ftl_policy_gc_victim_better(3U, 1U, 2U, 1U, 2U, 3U));
    emit(39U, cosmos_ftl_policy_gc_finish_action(5U, 1U));
    emit(40U, cosmos_ftl_policy_gc_step_status(1U, 1U, 0U, 1U, 0U, 0U));
    emit(41U, cosmos_ftl_policy_flush_action(1U, 1U, 0U, 3U));
    printf("FTL-ALLOC|scan-410|%u\n",
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 410U, 0U, 0U));
    printf("FTL-ALLOC|final-409|%u\n",
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 409U, 0U, 1U));
    printf("FTL-ALLOC|final-410|%u\n",
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 410U, 0U, 1U));
    printf("FTL-ALLOC|gc-final-409|%u\n",
           cosmos_ftl_policy_allocate_page_action(
               0U, 1U, 0U, 0U, 0U, 0U, 409U, 1U, 1U));
    return 0;
}
