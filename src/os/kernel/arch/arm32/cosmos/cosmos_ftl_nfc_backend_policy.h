#ifndef SIMPLE_COSMOS_FTL_NFC_BACKEND_POLICY_H
#define SIMPLE_COSMOS_FTL_NFC_BACKEND_POLICY_H

/* Scalar, allocation-free ABI emitted by cosmos_ftl_nfc_backend_policy.spl.
 * C retains MMIO/NAND/DMA, volatile/pointer access, CRC acquisition, callbacks,
 * byte serialization, and all side-effect sequencing. */
unsigned int cosmos_ftl_nfc_backend_policy_checkpoint_total_bytes(
    unsigned int l2p_count, unsigned int block_count);
int cosmos_ftl_nfc_backend_policy_header_prefix_status(
    unsigned int magic, unsigned int version, unsigned int header_crc,
    unsigned int expected_header_crc);
int cosmos_ftl_nfc_backend_policy_payload_length_status(
    unsigned int payload_length);
int cosmos_ftl_nfc_backend_policy_read_io_state(int status);
int cosmos_ftl_nfc_backend_policy_read_content_state(
    unsigned int all_ff, int header_status, unsigned int spare_header,
    int payload_status);
unsigned int cosmos_ftl_nfc_backend_policy_write_faults(int status);
int cosmos_ftl_nfc_backend_policy_superblock_status(
    int page_state, unsigned int page_type, unsigned long long logical_index,
    unsigned int payload_length, unsigned int payload_valid);
int cosmos_ftl_nfc_backend_policy_mounted_status(
    unsigned int backend_present, unsigned int mounted, unsigned int faulted);
unsigned int cosmos_ftl_nfc_backend_policy_checkpoint_candidate_better(
    unsigned int have_latest, unsigned long long candidate_generation,
    unsigned long long latest_generation, unsigned int candidate_segment,
    unsigned int latest_segment);
int cosmos_ftl_nfc_backend_policy_page_blank_status(int page_state);
int cosmos_ftl_nfc_backend_policy_recycle_status(
    unsigned int slot, unsigned int checkpoint_valid_mask);
unsigned long long cosmos_ftl_nfc_backend_policy_next_journal_index(
    unsigned long long current, unsigned long long checkpoint_index);
unsigned long long cosmos_ftl_nfc_backend_policy_first_journal_index(
    unsigned int checkpoint_valid_mask, unsigned long long current,
    unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1);
unsigned long long cosmos_ftl_nfc_backend_policy_journal_pages_normalized(
    unsigned long long journal_pages);
unsigned int cosmos_ftl_nfc_backend_policy_journal_pages_valid(
    unsigned long long journal_pages);
unsigned int cosmos_ftl_nfc_backend_policy_checkpoint_data_pages(
    unsigned int total_bytes);
unsigned int cosmos_ftl_nfc_backend_policy_checkpoint_slot_pages(
    unsigned long long journal_pages, unsigned int metadata_page_limit);
unsigned int cosmos_ftl_nfc_backend_policy_journal_start_page(
    unsigned int checkpoint_slot_pages);
unsigned int cosmos_ftl_nfc_backend_policy_layout_valid(
    unsigned int journal_start_page, unsigned long long journal_pages,
    unsigned int checkpoint_slot_pages, unsigned int checkpoint_record_pages,
    unsigned int metadata_page_limit);
unsigned int cosmos_ftl_nfc_backend_policy_journal_page(
    unsigned int journal_start_page, unsigned long long journal_capacity,
    unsigned long long index);
unsigned int cosmos_ftl_nfc_backend_policy_journal_append_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity,
    unsigned long long next_index);
unsigned int cosmos_ftl_nfc_backend_policy_journal_append_result(int status);
unsigned int cosmos_ftl_nfc_backend_policy_journal_read_admit(
    int mounted_status, unsigned long long index,
    unsigned long long first_index, unsigned long long capacity);
unsigned long long cosmos_ftl_nfc_backend_policy_journal_next_after_read(
    unsigned long long index, unsigned long long current);
unsigned int cosmos_ftl_nfc_backend_policy_journal_record_valid(
    unsigned long long sequence, unsigned long long expected_sequence,
    unsigned int magic, unsigned int crc, unsigned int expected_crc);
unsigned int cosmos_ftl_nfc_backend_policy_journal_block_fully_dead(
    unsigned long long capacity, unsigned long long next_index,
    unsigned int block, unsigned long long first_live);
int cosmos_ftl_nfc_backend_policy_journal_trim_status(
    int mounted_status, unsigned int checkpoint_valid_mask,
    unsigned long long first_live, unsigned long long first_index,
    unsigned long long capacity, unsigned long long checkpoint_index_0,
    unsigned long long checkpoint_index_1);

#endif
