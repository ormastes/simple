#include "cosmos_ftl_nfc_backend_policy_oracle.h"

#include <stdint.h>
#include <stdio.h>

#if defined(COSMOS_FTL_NFC_BACKEND_ORACLE_ONLY)
#define cosmos_ftl_nfc_backend_policy_checkpoint_total_bytes \
    cosmos_ftl_nfc_backend_oracle_checkpoint_total_bytes
#define cosmos_ftl_nfc_backend_policy_header_prefix_status \
    cosmos_ftl_nfc_backend_oracle_header_prefix_status
#define cosmos_ftl_nfc_backend_policy_payload_length_status \
    cosmos_ftl_nfc_backend_oracle_payload_length_status
#define cosmos_ftl_nfc_backend_policy_read_io_state \
    cosmos_ftl_nfc_backend_oracle_read_io_state
#define cosmos_ftl_nfc_backend_policy_read_content_state \
    cosmos_ftl_nfc_backend_oracle_read_content_state
#define cosmos_ftl_nfc_backend_policy_write_faults \
    cosmos_ftl_nfc_backend_oracle_write_faults
#define cosmos_ftl_nfc_backend_policy_superblock_status \
    cosmos_ftl_nfc_backend_oracle_superblock_status
#define cosmos_ftl_nfc_backend_policy_mounted_status \
    cosmos_ftl_nfc_backend_oracle_mounted_status
#define cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better \
    cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better
#define cosmos_ftl_nfc_backend_policy_page_blank_status \
    cosmos_ftl_nfc_backend_oracle_page_blank_status
#define cosmos_ftl_nfc_backend_policy_recycle_status \
    cosmos_ftl_nfc_backend_oracle_recycle_status
#define cosmos_ftl_nfc_backend_policy_next_journal_index \
    cosmos_ftl_nfc_backend_oracle_next_journal_index
#define cosmos_ftl_nfc_backend_policy_first_journal_index \
    cosmos_ftl_nfc_backend_oracle_first_journal_index
#define cosmos_ftl_nfc_backend_policy_journal_pages_normalized \
    cosmos_ftl_nfc_backend_oracle_journal_pages_normalized
#define cosmos_ftl_nfc_backend_policy_journal_pages_valid \
    cosmos_ftl_nfc_backend_oracle_journal_pages_valid
#define cosmos_ftl_nfc_backend_policy_checkpoint_data_pages \
    cosmos_ftl_nfc_backend_oracle_checkpoint_data_pages
#define cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages \
    cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages
#define cosmos_ftl_nfc_backend_policy_journal_start_page \
    cosmos_ftl_nfc_backend_oracle_journal_start_page
#define cosmos_ftl_nfc_backend_policy_layout_valid \
    cosmos_ftl_nfc_backend_oracle_layout_valid
#define cosmos_ftl_nfc_backend_policy_journal_page \
    cosmos_ftl_nfc_backend_oracle_journal_page
#define cosmos_ftl_nfc_backend_policy_journal_append_admit \
    cosmos_ftl_nfc_backend_oracle_journal_append_admit
#define cosmos_ftl_nfc_backend_policy_journal_append_result \
    cosmos_ftl_nfc_backend_oracle_journal_append_result
#define cosmos_ftl_nfc_backend_policy_journal_read_admit \
    cosmos_ftl_nfc_backend_oracle_journal_read_admit
#define cosmos_ftl_nfc_backend_policy_journal_next_after_read \
    cosmos_ftl_nfc_backend_oracle_journal_next_after_read
#define cosmos_ftl_nfc_backend_policy_journal_record_valid \
    cosmos_ftl_nfc_backend_oracle_journal_record_valid
#define cosmos_ftl_nfc_backend_policy_journal_block_fully_dead \
    cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead
#define cosmos_ftl_nfc_backend_policy_journal_trim_status \
    cosmos_ftl_nfc_backend_oracle_journal_trim_status
#else
#include "cosmos_ftl_nfc_backend_policy.h"
#endif

static unsigned int rows;

#define CHECK_VALUE(actual, expected) do { \
    unsigned long long actual_value = (unsigned long long)(actual); \
    unsigned long long expected_value = (unsigned long long)(expected); \
    ++rows; \
    if (actual_value != expected_value) { \
        fprintf(stderr, "parity row %u: actual=%llu expected=%llu\n", \
                rows, actual_value, expected_value); \
        return 1; \
    } \
} while (0)

#define CHECK_EXACT(actual, oracle, exact) do { \
    unsigned long long actual_value = (unsigned long long)(actual); \
    unsigned long long oracle_value = (unsigned long long)(oracle); \
    unsigned long long exact_value = (unsigned long long)(exact); \
    ++rows; \
    if (actual_value != oracle_value || actual_value != exact_value) { \
        fprintf(stderr, \
                "boundary row %u: actual=%llu oracle=%llu exact=%llu\n", \
                rows, actual_value, oracle_value, exact_value); \
        return 1; \
    } \
} while (0)

int main(void) {
    unsigned int i;
    const unsigned long long normalized_cases[] = {0ULL, 65536ULL};
    const unsigned long long journal_valid_cases[] = {
        65536ULL, 262145ULL, 3ULL, 64ULL, 128ULL
    };
    const int append_statuses[] = {0, 1, 2, 3, 4, 5, 6};

    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_total_bytes(1U, 1U), cosmos_ftl_nfc_backend_oracle_checkpoint_total_bytes(1U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_total_bytes(UINT32_MAX, UINT32_MAX), cosmos_ftl_nfc_backend_oracle_checkpoint_total_bytes(UINT32_MAX, UINT32_MAX));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_header_prefix_status(0x43464E31U, 1U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_header_prefix_status(0x43464E31U, 1U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_header_prefix_status(0U, 1U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_header_prefix_status(0U, 1U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_header_prefix_status(0x43464E31U, 2U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_header_prefix_status(0x43464E31U, 2U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_header_prefix_status(0x43464E31U, 1U, 7U, 8U), cosmos_ftl_nfc_backend_oracle_header_prefix_status(0x43464E31U, 1U, 7U, 8U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_payload_length_status(16348U), cosmos_ftl_nfc_backend_oracle_payload_length_status(16348U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_payload_length_status(16349U), cosmos_ftl_nfc_backend_oracle_payload_length_status(16349U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_io_state(0), cosmos_ftl_nfc_backend_oracle_read_io_state(0));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_io_state(5), cosmos_ftl_nfc_backend_oracle_read_io_state(5));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_io_state(4), cosmos_ftl_nfc_backend_oracle_read_io_state(4));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_content_state(1U, 2, 0U, 2), cosmos_ftl_nfc_backend_oracle_read_content_state(1U, 2, 0U, 2));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_content_state(0U, 2, 0U, 0), cosmos_ftl_nfc_backend_oracle_read_content_state(0U, 2, 0U, 0));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_content_state(0U, 0, 0U, 2), cosmos_ftl_nfc_backend_oracle_read_content_state(0U, 0, 0U, 2));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_content_state(0U, 0, 0U, 0), cosmos_ftl_nfc_backend_oracle_read_content_state(0U, 0, 0U, 0));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_read_content_state(0U, 0, 1U, 2), cosmos_ftl_nfc_backend_oracle_read_content_state(0U, 0, 1U, 2));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_write_faults(0), cosmos_ftl_nfc_backend_oracle_write_faults(0));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_write_faults(3), cosmos_ftl_nfc_backend_oracle_write_faults(3));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_write_faults(6), cosmos_ftl_nfc_backend_oracle_write_faults(6));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_write_faults(4), cosmos_ftl_nfc_backend_oracle_write_faults(4));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(1, 1U, 0ULL, 40U, 1U), cosmos_ftl_nfc_backend_oracle_superblock_status(1, 1U, 0ULL, 40U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(3, 0U, 0ULL, 0U, 0U), cosmos_ftl_nfc_backend_oracle_superblock_status(3, 0U, 0ULL, 0U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(0, 0U, 0ULL, 0U, 0U), cosmos_ftl_nfc_backend_oracle_superblock_status(0, 0U, 0ULL, 0U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(4, 0U, 0ULL, 0U, 0U), cosmos_ftl_nfc_backend_oracle_superblock_status(4, 0U, 0ULL, 0U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(1, 2U, 0ULL, 40U, 1U), cosmos_ftl_nfc_backend_oracle_superblock_status(1, 2U, 0ULL, 40U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(1, 1U, 1ULL, 40U, 1U), cosmos_ftl_nfc_backend_oracle_superblock_status(1, 1U, 1ULL, 40U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(1, 1U, 0ULL, 39U, 1U), cosmos_ftl_nfc_backend_oracle_superblock_status(1, 1U, 0ULL, 39U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_superblock_status(1, 1U, 0ULL, 40U, 0U), cosmos_ftl_nfc_backend_oracle_superblock_status(1, 1U, 0ULL, 40U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_mounted_status(1U, 1U, 0U), cosmos_ftl_nfc_backend_oracle_mounted_status(1U, 1U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_mounted_status(0U, 1U, 0U), cosmos_ftl_nfc_backend_oracle_mounted_status(0U, 1U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_mounted_status(1U, 0U, 0U), cosmos_ftl_nfc_backend_oracle_mounted_status(1U, 0U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_mounted_status(1U, 1U, 1U), cosmos_ftl_nfc_backend_oracle_mounted_status(1U, 1U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(0U, 1ULL, 9ULL, 0U, 9U), cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(0U, 1ULL, 9ULL, 0U, 9U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(1U, 2ULL, 1ULL, 0U, 9U), cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(1U, 2ULL, 1ULL, 0U, 9U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(1U, 1ULL, 2ULL, 9U, 0U), cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(1U, 1ULL, 2ULL, 9U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(1U, 2ULL, 2ULL, 2U, 1U), cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(1U, 2ULL, 2ULL, 2U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(1U, 2ULL, 2ULL, 1U, 2U), cosmos_ftl_nfc_backend_oracle_checkpoint_candidate_better(1U, 2ULL, 2ULL, 1U, 2U));
    for (i = 0U; i < 5U; ++i) {
        int state = (const int[]){0, 3, 4, 1, 2}[i];
        CHECK_VALUE(cosmos_ftl_nfc_backend_policy_page_blank_status(state), cosmos_ftl_nfc_backend_oracle_page_blank_status(state));
    }
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_recycle_status(2U, 3U), cosmos_ftl_nfc_backend_oracle_recycle_status(2U, 3U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_recycle_status(0U, 0U), cosmos_ftl_nfc_backend_oracle_recycle_status(0U, 0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_recycle_status(0U, 2U), cosmos_ftl_nfc_backend_oracle_recycle_status(0U, 2U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_recycle_status(1U, 1U), cosmos_ftl_nfc_backend_oracle_recycle_status(1U, 1U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_next_journal_index(2ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_next_journal_index(2ULL, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_next_journal_index(3ULL, 2ULL), cosmos_ftl_nfc_backend_oracle_next_journal_index(3ULL, 2ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_first_journal_index(1U, 4ULL, 8ULL, 9ULL), cosmos_ftl_nfc_backend_oracle_first_journal_index(1U, 4ULL, 8ULL, 9ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_first_journal_index(3U, 4ULL, 8ULL, 7ULL), cosmos_ftl_nfc_backend_oracle_first_journal_index(3U, 4ULL, 8ULL, 7ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_first_journal_index(3U, 4ULL, 7ULL, 8ULL), cosmos_ftl_nfc_backend_oracle_first_journal_index(3U, 4ULL, 7ULL, 8ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_first_journal_index(3U, 9ULL, 7ULL, 8ULL), cosmos_ftl_nfc_backend_oracle_first_journal_index(3U, 9ULL, 7ULL, 8ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_first_journal_index(3U, 7ULL, 7ULL, 8ULL), cosmos_ftl_nfc_backend_oracle_first_journal_index(3U, 7ULL, 7ULL, 8ULL));
    for (i = 0U; i < 2U; ++i) CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_pages_normalized(normalized_cases[i]), cosmos_ftl_nfc_backend_oracle_journal_pages_normalized(normalized_cases[i]));
    for (i = 0U; i < 5U; ++i) CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_pages_valid(journal_valid_cases[i]), cosmos_ftl_nfc_backend_oracle_journal_pages_valid(journal_valid_cases[i]));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_pages_valid(0ULL), cosmos_ftl_nfc_backend_oracle_journal_pages_valid(0ULL), 0U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_data_pages(0U), cosmos_ftl_nfc_backend_oracle_checkpoint_data_pages(0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_data_pages(16349U), cosmos_ftl_nfc_backend_oracle_checkpoint_data_pages(16349U));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_checkpoint_data_pages(UINT32_MAX), cosmos_ftl_nfc_backend_oracle_checkpoint_data_pages(UINT32_MAX), 262722U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(256ULL, 1024U), cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(256ULL, 1024U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(262144ULL, 524288U), cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(262144ULL, 524288U));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(0ULL, 127U), cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(0ULL, 127U), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(897ULL, 1024U), cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(897ULL, 1024U), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(UINT64_MAX, 1024U), cosmos_ftl_nfc_backend_oracle_checkpoint_slot_pages(UINT64_MAX, 1024U), 0U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_start_page(0U), cosmos_ftl_nfc_backend_oracle_journal_start_page(0U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_start_page(128U), cosmos_ftl_nfc_backend_oracle_journal_start_page(128U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_layout_valid(128U, 128ULL, 128U, 2U, 1024U), cosmos_ftl_nfc_backend_oracle_layout_valid(128U, 128ULL, 128U, 2U, 1024U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_layout_valid(1024U, 128ULL, 128U, 2U, 1024U), cosmos_ftl_nfc_backend_oracle_layout_valid(1024U, 128ULL, 128U, 2U, 1024U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_layout_valid(1000U, 128ULL, 128U, 2U, 1024U), cosmos_ftl_nfc_backend_oracle_layout_valid(1000U, 128ULL, 128U, 2U, 1024U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_layout_valid(128U, 128ULL, 1U, 2U, 1024U), cosmos_ftl_nfc_backend_oracle_layout_valid(128U, 128ULL, 1U, 2U, 1024U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_page(100U, 256ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_page(100U, 256ULL, 0ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_page(100U, 256ULL, 255ULL), cosmos_ftl_nfc_backend_oracle_journal_page(100U, 256ULL, 255ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_page(100U, 256ULL, 256ULL), cosmos_ftl_nfc_backend_oracle_journal_page(100U, 256ULL, 256ULL));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_page(100U, 0ULL, 1ULL), cosmos_ftl_nfc_backend_oracle_journal_page(100U, 0ULL, 1ULL), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_page(100U, 3ULL, 1ULL), cosmos_ftl_nfc_backend_oracle_journal_page(100U, 3ULL, 1ULL), 0U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(1, 3ULL, 2ULL, 4ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(1, 3ULL, 2ULL, 4ULL, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 1ULL, 2ULL, 4ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 1ULL, 2ULL, 4ULL, 0ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 6ULL, 2ULL, 4ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 6ULL, 2ULL, 4ULL, 0ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 4ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 4ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 3ULL, 2ULL, 4ULL, 0ULL));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 3ULL, 2ULL, 0ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 3ULL, 2ULL, 0ULL, 0ULL), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_append_admit(0, 3ULL, 2ULL, 3ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_append_admit(0, 3ULL, 2ULL, 3ULL, 0ULL), 0U);
    for (i = 0U; i < 7U; ++i) CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_append_result(append_statuses[i]), cosmos_ftl_nfc_backend_oracle_journal_append_result(append_statuses[i]));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_read_admit(1, 3ULL, 2ULL, 4ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(1, 3ULL, 2ULL, 4ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_read_admit(0, 1ULL, 2ULL, 4ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(0, 1ULL, 2ULL, 4ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_read_admit(0, 6ULL, 2ULL, 4ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(0, 6ULL, 2ULL, 4ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_read_admit(0, 3ULL, 2ULL, 4ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(0, 3ULL, 2ULL, 4ULL));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_read_admit(0, 3ULL, 2ULL, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(0, 3ULL, 2ULL, 0ULL), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_read_admit(0, 3ULL, 2ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_read_admit(0, 3ULL, 2ULL, 3ULL), 0U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_next_after_read(UINT64_MAX, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_next_after_read(UINT64_MAX, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_next_after_read(3ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_next_after_read(3ULL, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_next_after_read(2ULL, 3ULL), cosmos_ftl_nfc_backend_oracle_journal_next_after_read(2ULL, 3ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_record_valid(1ULL, 1ULL, 0x46544C31U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_journal_record_valid(1ULL, 1ULL, 0x46544C31U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_record_valid(1ULL, 2ULL, 0x46544C31U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_journal_record_valid(1ULL, 2ULL, 0x46544C31U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_record_valid(1ULL, 1ULL, 0U, 7U, 7U), cosmos_ftl_nfc_backend_oracle_journal_record_valid(1ULL, 1ULL, 0U, 7U, 7U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_record_valid(1ULL, 1ULL, 0x46544C31U, 7U, 8U), cosmos_ftl_nfc_backend_oracle_journal_record_valid(1ULL, 1ULL, 0x46544C31U, 7U, 8U));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(256ULL, 0ULL, 0U, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(256ULL, 0ULL, 0U, 0ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(128ULL, 128ULL, 0U, 128ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(128ULL, 128ULL, 0U, 128ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(256ULL, 300ULL, 0U, 384ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(256ULL, 300ULL, 0U, 384ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(256ULL, 300ULL, 0U, 383ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(256ULL, 300ULL, 0U, 383ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(1ULL, UINT64_MAX - 64ULL, 0U, UINT64_MAX), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(1ULL, UINT64_MAX - 64ULL, 0U, UINT64_MAX));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(0ULL, 0ULL, 0U, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(0ULL, 0ULL, 0U, 0ULL), 0U);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(3ULL, 0ULL, 0U, 0ULL), cosmos_ftl_nfc_backend_oracle_journal_block_fully_dead(3ULL, 0ULL, 0U, 0ULL), 0U);
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(1, 3U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(1, 3U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 1U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 1U, 4ULL, 2ULL, 4ULL, 5ULL, 6ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 1ULL, 2ULL, 4ULL, 5ULL, 6ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 1ULL, 2ULL, 4ULL, 5ULL, 6ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 7ULL, 2ULL, 4ULL, 8ULL, 9ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 7ULL, 2ULL, 4ULL, 8ULL, 9ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 7ULL, 2ULL, 8ULL, 8ULL, 7ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 7ULL, 2ULL, 8ULL, 8ULL, 7ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 7ULL, 2ULL, 8ULL, 7ULL, 8ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 7ULL, 2ULL, 8ULL, 7ULL, 8ULL));
    CHECK_VALUE(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 8ULL, 2ULL, 8ULL, 7ULL, 9ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 8ULL, 2ULL, 8ULL, 7ULL, 9ULL));
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 2ULL, 2ULL, 0ULL, 2ULL, 2ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 2ULL, 2ULL, 0ULL, 2ULL, 2ULL), 1);
    CHECK_EXACT(cosmos_ftl_nfc_backend_policy_journal_trim_status(0, 3U, 2ULL, 2ULL, 3ULL, 2ULL, 2ULL), cosmos_ftl_nfc_backend_oracle_journal_trim_status(0, 3U, 2ULL, 2ULL, 3ULL, 2ULL, 2ULL), 1);

    printf("COSMOS_FTL_NFC_BACKEND_PARITY_ROWS %u\n", rows);
    return 0;
}
