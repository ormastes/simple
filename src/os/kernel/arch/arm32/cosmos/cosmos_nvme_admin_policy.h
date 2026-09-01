#ifndef SIMPLE_COSMOS_NVME_ADMIN_POLICY_H
#define SIMPLE_COSMOS_NVME_ADMIN_POLICY_H

/* Allocation-free scalar ABI exported by cosmos_nvme_admin_policy.spl. */
#define COSMOS_NVME_ADMIN_POLICY_CONTINUE 0xFFFFFFFFU

unsigned int cosmos_nvme_admin_policy_status_success(void);
unsigned int cosmos_nvme_admin_policy_status_generic(unsigned int sc);
unsigned int cosmos_nvme_admin_policy_status_specific(unsigned int sc);
unsigned int cosmos_nvme_admin_policy_min(unsigned int left,
                                           unsigned int right);
int cosmos_nvme_admin_policy_power_of_two(unsigned int value);
unsigned int cosmos_nvme_admin_policy_log2(unsigned int value);
int cosmos_nvme_admin_policy_no_payload(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes);
int cosmos_nvme_admin_policy_queue_base_valid(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes);
int cosmos_nvme_admin_policy_opcode_supported(unsigned int opcode);
int cosmos_nvme_admin_policy_payload_valid(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int payload_bytes,
    unsigned int required_bytes);
int cosmos_nvme_admin_policy_queue_index_valid(unsigned int queue_id);
int cosmos_nvme_admin_policy_queue_id_allowed(
    unsigned int negotiated_count, unsigned int queue_id);
int cosmos_nvme_admin_policy_controller_namespace_valid(
    unsigned int namespace_id);
int cosmos_nvme_admin_policy_smart_namespace_valid(unsigned int namespace_id);
unsigned int cosmos_nvme_admin_policy_publish_state(unsigned int post_result);
int cosmos_nvme_admin_policy_publish_result(unsigned int post_result);
unsigned int cosmos_nvme_admin_policy_payload_status(
    unsigned int valid, unsigned int payload_result);
unsigned int cosmos_nvme_admin_policy_identify_status(
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_policy_get_log_status(
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_policy_set_features_status(
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_policy_queue_count(unsigned int cdw11);
unsigned int cosmos_nvme_admin_policy_queue_result(unsigned int queue_count);
unsigned int cosmos_nvme_admin_policy_get_features_status(
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_policy_create_cq_status(
    unsigned int negotiated, unsigned int existing_valid,
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13, unsigned int low1,
    unsigned int high1, unsigned int low2, unsigned int high2,
    unsigned int bytes);
unsigned int cosmos_nvme_admin_policy_create_sq_status(
    unsigned int negotiated, unsigned int completion_valid,
    unsigned int existing_valid, unsigned int namespace_id,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_policy_delete_sq_status(
    unsigned int negotiated, unsigned int existing_valid,
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13, unsigned int low1,
    unsigned int high1, unsigned int low2, unsigned int high2,
    unsigned int bytes);
unsigned int cosmos_nvme_admin_policy_delete_cq_status(
    unsigned int negotiated, unsigned int existing_valid,
    unsigned int has_dependent_sq, unsigned int namespace_id,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_policy_abort_status(
    unsigned int negotiated, unsigned int target_sq_valid,
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_policy_abort_result(
    unsigned int target_queue_id, unsigned int target_cid,
    unsigned int aer_pending, unsigned int aer_cid);
unsigned int cosmos_nvme_admin_policy_envelope_status(
    unsigned int invalid_field, unsigned int queue_id, unsigned int cid,
    unsigned int opcode, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_policy_async_event_status(
    unsigned int callback_present, unsigned int pending,
    unsigned int namespace_id, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
int cosmos_nvme_admin_policy_init_values_valid(
    unsigned int blocks_low, unsigned int blocks_high,
    unsigned int block_bytes);
unsigned int cosmos_nvme_admin_policy_adapter_failure_status(int result);

#endif
