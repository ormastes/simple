#ifndef SIMPLE_COSMOS_NVME_MEDIA_POLICY_H
#define SIMPLE_COSMOS_NVME_MEDIA_POLICY_H

/*
 * Allocation-free scalar ABI exported by cosmos_nvme_media_policy.spl.
 * C retains all pointers, volatile storage, atomics, and callback invocation.
 */
#define COSMOS_NVME_MEDIA_POLICY_ABI_VERSION 1U
#define COSMOS_NVME_MEDIA_POLICY_FUNCTIONS 36U
#define COSMOS_NVME_MEDIA_POLICY_DECISIONS 63U
#define COSMOS_NVME_MEDIA_POLICY_BRANCH_OUTCOMES 126U

#define COSMOS_NVME_MEDIA_POLICY_CONTINUE 0xFFFFFFFFU

#define COSMOS_NVME_MEDIA_PAGE_FULL_WRITE 0U
#define COSMOS_NVME_MEDIA_PAGE_READ_MAPPED 1U
#define COSMOS_NVME_MEDIA_PAGE_ZERO_UNMAPPED 2U
#define COSMOS_NVME_MEDIA_PAGE_PROPAGATE 3U

unsigned int cosmos_nvme_media_policy_status_success(void);
unsigned int cosmos_nvme_media_policy_status_invalid_opcode(void);
unsigned int cosmos_nvme_media_policy_status_invalid_field(void);
unsigned int cosmos_nvme_media_policy_status_invalid_namespace(void);
unsigned int cosmos_nvme_media_policy_status_lba_range(void);
unsigned int cosmos_nvme_media_policy_status_data_transfer(void);
int cosmos_nvme_media_policy_status_is_success(unsigned int encoded);
unsigned int cosmos_nvme_media_policy_media_status(
    int result, unsigned int media_sc);

int cosmos_nvme_media_policy_end_within_namespace(
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int lba_low, unsigned int lba_high,
    unsigned int block_count);
int cosmos_nvme_media_policy_data_span_valid(
    unsigned int address_low, unsigned int address_high,
    unsigned int address2_low, unsigned int address2_high,
    unsigned int data_bytes, unsigned int required_bytes);
unsigned int cosmos_nvme_media_policy_rw_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int block_bytes);
unsigned int cosmos_nvme_media_policy_flush_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int address_low, unsigned int address_high,
    unsigned int address2_low, unsigned int address2_high,
    unsigned int data_bytes);
unsigned int cosmos_nvme_media_policy_zeroes_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int callback_present);
unsigned int cosmos_nvme_media_policy_dsm_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int callback_present);
unsigned int cosmos_nvme_media_policy_post_state(unsigned int post_result);
int cosmos_nvme_media_policy_post_status(unsigned int post_result);
int cosmos_nvme_media_policy_service_init_valid(
    unsigned int post_present, unsigned int read_present,
    unsigned int program_present, unsigned int flush_present,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int block_bytes);

int cosmos_nvme_media_policy_dispatch_init_valid(
    unsigned int dispatch_present, unsigned int bridge_present,
    unsigned int io_present, unsigned int admin_present,
    unsigned int io_fetch_present, unsigned int admin_fetch_present);
int cosmos_nvme_media_policy_dispatch_queue_status(
    unsigned int queue_id, unsigned int negotiated_queue_count,
    unsigned int submission_valid, unsigned int completion_queue_id,
    unsigned int completion_valid);

unsigned long long cosmos_nvme_media_policy_u64(
    unsigned int low, unsigned int high);
int cosmos_nvme_media_policy_address_set_valid(
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address);
int cosmos_nvme_media_policy_command_span_status(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int data_bytes,
    unsigned int slot_tag, unsigned int lba_low, unsigned int lba_high,
    unsigned int namespace_low, unsigned int namespace_high);
int cosmos_nvme_media_policy_zeroes_span_status(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int data_bytes,
    unsigned int slot_tag, unsigned int lba_low, unsigned int lba_high,
    unsigned int nlb, unsigned int namespace_low,
    unsigned int namespace_high);
unsigned int cosmos_nvme_media_policy_retry_limit(unsigned int configured);
unsigned int cosmos_nvme_media_policy_command_retry_limit(
    unsigned int control, unsigned int limited_retry_mask);
int cosmos_nvme_media_policy_begin_status(
    unsigned int media_present, unsigned int ftl_present,
    unsigned int prior_busy);
int cosmos_nvme_media_policy_retry_terminal(
    int status, unsigned int attempt, unsigned int limit);
int cosmos_nvme_media_policy_mapped_read_status(
    int status, unsigned int actual_lpn, unsigned int expected_lpn);
int cosmos_nvme_media_policy_dma_offsets_valid(
    unsigned int command_offset, unsigned int device_offset);
unsigned int cosmos_nvme_media_policy_page_action(
    int lookup_status, unsigned int write,
    unsigned int page_offset, unsigned int page_count);
unsigned int cosmos_nvme_media_policy_page_count(
    unsigned int page_offset, unsigned int remaining);
int cosmos_nvme_media_policy_dsm_range_valid(
    unsigned int attributes, unsigned int length,
    unsigned long long starting_lba,
    unsigned int namespace_low, unsigned int namespace_high);
int cosmos_nvme_media_policy_init_valid(
    unsigned int media_present, unsigned int ftl_present,
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address);
int cosmos_nvme_media_policy_deallocate_valid(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int data_bytes,
    unsigned int slot_tag);
unsigned int cosmos_nvme_media_policy_chunk_bytes(unsigned int remaining);
int cosmos_nvme_media_policy_full_page(unsigned int page_offset,
                                        unsigned int page_count);

#endif
