#ifndef SIMPLE_COSMOS_FTL_POLICY_H
#define SIMPLE_COSMOS_FTL_POLICY_H

/* Scalar C ABI exported by cosmos_ftl_policy.spl.  Pointer traversal,
 * callbacks, table acquisition, and writeback deliberately stay out of this
 * interface. */
unsigned int cosmos_ftl_policy_crc32_step(unsigned int crc,
                                           unsigned int byte);
unsigned int cosmos_ftl_policy_crc32_begin(unsigned int bytes);
unsigned int cosmos_ftl_policy_crc32_u32(unsigned int crc,
                                          unsigned int value);
unsigned int cosmos_ftl_policy_crc32_u64(unsigned int crc,
                                          unsigned long long value);
unsigned int cosmos_ftl_policy_checkpoint_crc(
    unsigned int magic, unsigned int version, unsigned long long generation,
    unsigned long long journal_index, unsigned int l2p_count,
    unsigned int block_count, unsigned int allocation_lane,
    unsigned int journal_crc, unsigned int l2p_crc, unsigned int block_crc);
unsigned int cosmos_ftl_policy_journal_record_crc(
    unsigned int magic, unsigned int type, unsigned long long sequence,
    unsigned long long generation, unsigned int lpn, unsigned int new_ppa,
    unsigned int old_ppa, unsigned int block_index,
    unsigned int previous_crc);
unsigned int cosmos_ftl_policy_l2p_crc_step(unsigned int crc,
                                             unsigned int value);
unsigned int cosmos_ftl_policy_blocks_crc_step(
    unsigned int crc, unsigned int valid_pages, unsigned int erase_count,
    unsigned int bad, unsigned int state, unsigned int next_page,
    unsigned int reserved);
unsigned long long cosmos_ftl_policy_ppa_encode(
    unsigned int die, unsigned int lun, unsigned int block,
    unsigned int page);
unsigned int cosmos_ftl_policy_ppa_decode_valid(unsigned int ppa);
unsigned long long cosmos_ftl_policy_ppa_row(unsigned int ppa);
unsigned int cosmos_ftl_policy_block_index_from_parts(
    unsigned int die, unsigned int lun, unsigned int block);
unsigned int cosmos_ftl_policy_lane_index_from_parts(
    unsigned int die, unsigned int lun);
unsigned long long cosmos_ftl_policy_block_parts_from_index(
    unsigned int index);
unsigned long long cosmos_ftl_policy_block_index_from_ppa(unsigned int ppa);
unsigned long long cosmos_ftl_policy_clear_tables_value(unsigned int kind);
unsigned int cosmos_ftl_policy_init_valid(
    unsigned int ftl_present, unsigned int backend_present,
    unsigned int l2p_present, unsigned int l2p_count,
    unsigned int blocks_present, unsigned int namespace_pages,
    unsigned int block_count, unsigned int expected_blocks,
    unsigned int callback_mask, unsigned long long journal_capacity);
unsigned int cosmos_ftl_policy_factory_initialize_erased_valid(
    unsigned int ftl_present);
unsigned int cosmos_ftl_policy_factory_block_state(unsigned int block,
                                                     unsigned int bad);
unsigned int cosmos_ftl_policy_checkpoint_valid(
    unsigned int magic, unsigned int version, unsigned int l2p_count,
    unsigned int expected_l2p_count, unsigned int block_count,
    unsigned int expected_block_count, unsigned int header_crc,
    unsigned int expected_header_crc);
unsigned int cosmos_ftl_policy_load_checkpoint_status(
    unsigned int backend_status, unsigned int l2p_crc,
    unsigned int expected_l2p_crc, unsigned int block_crc,
    unsigned int expected_block_crc, unsigned int allocation_lane);
unsigned int cosmos_ftl_policy_map_apply_actions(
    unsigned int old_ppa, unsigned int old_index_valid,
    unsigned int old_valid_pages, unsigned int new_index_valid);
unsigned int cosmos_ftl_policy_rebuild_runtime_state_entry(
    unsigned int block, unsigned int valid_pages, unsigned int bad,
    unsigned int state, unsigned int next_page, unsigned int reserved,
    unsigned int lane_has_open);
unsigned int cosmos_ftl_policy_allocation_ppa_valid(
    unsigned int ppa_valid, unsigned int block, unsigned int page,
    unsigned int bad, unsigned int state, unsigned int open_block);
unsigned long long cosmos_ftl_policy_allocation_apply_receipt(
    unsigned int state, unsigned int page, unsigned int block,
    unsigned int lane);
unsigned int cosmos_ftl_policy_apply_record_action(
    unsigned int record_type, unsigned int lpn, unsigned int l2p_count,
    unsigned int block_index, unsigned int block_count);
unsigned int cosmos_ftl_policy_data_ppa_valid(
    unsigned int ppa_valid, unsigned int block,
    unsigned int block_index_valid, unsigned int bad);
unsigned int cosmos_ftl_policy_journal_has_space(
    unsigned long long journal_index, unsigned long long journal_first_index,
    unsigned long long capacity, unsigned long long records);
unsigned int cosmos_ftl_policy_recover_checkpoint_first(
    unsigned int valid0, unsigned int valid1,
    unsigned long long generation0, unsigned long long generation1,
    unsigned long long journal0, unsigned long long journal1);
unsigned int cosmos_ftl_policy_lookup_status(
    unsigned int ftl_present, unsigned int ppa_present, unsigned int mounted,
    unsigned int lpn, unsigned int l2p_count, unsigned int mapped_ppa,
    unsigned int index_valid, unsigned int bad);
unsigned int cosmos_ftl_policy_append_record_result(
    unsigned long long journal_index, unsigned long long journal_first_index,
    unsigned long long capacity, unsigned int append_result);
unsigned int cosmos_ftl_policy_allocate_page_action(
    unsigned int index, unsigned int excluded_index, unsigned int state,
    unsigned int next_page, unsigned int bad,
    unsigned int is_open_candidate, unsigned int free_count,
    unsigned int gc, unsigned int free_count_is_final);
unsigned int cosmos_ftl_policy_commit_page_admit(
    unsigned int ftl_present, unsigned int ppa_present, unsigned int mounted,
    unsigned int fail_sticky, unsigned int lpn, unsigned int l2p_count,
    unsigned long long generation, unsigned int journal_space,
    unsigned int source_ppa, unsigned int source_index_valid);
unsigned int cosmos_ftl_policy_commit_page_mode(unsigned int source_ppa);
unsigned int cosmos_ftl_policy_refresh_page_status(
    unsigned int lookup_status, unsigned int mapped_ppa,
    unsigned int source_ppa);
unsigned int cosmos_ftl_policy_discard_page_action(
    unsigned int ftl_present, unsigned int mounted, unsigned int fail_sticky,
    unsigned int lpn, unsigned int l2p_count,
    unsigned long long generation, unsigned int old_ppa,
    unsigned int journal_space);
unsigned int cosmos_ftl_policy_retire_block_action(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int index_valid, unsigned int state,
    unsigned int valid_pages, unsigned int journal_space);
unsigned int cosmos_ftl_policy_gc_victim_better(
    unsigned int state, unsigned int valid_pages, unsigned int erase_count,
    unsigned int best_present, unsigned int best_valid,
    unsigned int best_erase_count);
unsigned int cosmos_ftl_policy_gc_finish_action(unsigned int state,
                                                 unsigned int journal_space);
unsigned int cosmos_ftl_policy_gc_step_status(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int fail_sticky, unsigned int max_moves,
    unsigned int moves, unsigned int victim_status);
unsigned int cosmos_ftl_policy_flush_action(
    unsigned int ftl_present, unsigned int mounted,
    unsigned int fail_sticky,
    unsigned int checkpoint_valid_mask_after_write);

#endif
