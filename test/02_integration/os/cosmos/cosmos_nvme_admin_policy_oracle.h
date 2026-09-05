#ifndef SIMPLE_TEST_COSMOS_NVME_ADMIN_POLICY_ORACLE_H
#define SIMPLE_TEST_COSMOS_NVME_ADMIN_POLICY_ORACLE_H

/* Frozen independently named copy of the pre-migration C decisions. */
unsigned int cosmos_nvme_admin_oracle_status_success(void);
unsigned int cosmos_nvme_admin_oracle_status_generic(unsigned int sc);
unsigned int cosmos_nvme_admin_oracle_identify_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_oracle_get_log_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_oracle_set_features_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_oracle_get_features_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13);
unsigned int cosmos_nvme_admin_oracle_create_cq_status(
    unsigned int negotiated, unsigned int existing, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_oracle_create_sq_status(
    unsigned int negotiated, unsigned int completion_valid,
    unsigned int existing, unsigned int nsid, unsigned int cdw10,
    unsigned int cdw11, unsigned int cdw12, unsigned int cdw13,
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_oracle_delete_sq_status(
    unsigned int negotiated, unsigned int existing, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_oracle_delete_cq_status(
    unsigned int negotiated, unsigned int existing, unsigned int dependent,
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13, unsigned int low1,
    unsigned int high1, unsigned int low2, unsigned int high2,
    unsigned int bytes);
unsigned int cosmos_nvme_admin_oracle_abort_status(
    unsigned int negotiated, unsigned int sq_valid, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13);
unsigned int cosmos_nvme_admin_oracle_envelope_status(
    unsigned int invalid, unsigned int queue_id, unsigned int cid,
    unsigned int opcode, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_admin_oracle_async_event_status(
    unsigned int callback, unsigned int pending, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13);
int cosmos_nvme_admin_oracle_frozen_selfcheck(void);

#endif
