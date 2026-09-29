#ifndef SIMPLE_TEST_COSMOS_NVME_PCIE_ADAPTER_POLICY_ORACLE_H
#define SIMPLE_TEST_COSMOS_NVME_PCIE_ADAPTER_POLICY_ORACLE_H

/* Independently named frozen copy of the pre-migration C scalar policy. */
unsigned int cosmos_nvme_pcie_adapter_oracle_command_cid(unsigned int dw0);
unsigned int cosmos_nvme_pcie_adapter_oracle_command_opcode(unsigned int dw0);
int cosmos_nvme_pcie_adapter_oracle_capacity_valid(
    unsigned int low, unsigned int high);
int cosmos_nvme_pcie_adapter_oracle_block_bytes_valid(unsigned int bytes);
int cosmos_nvme_pcie_adapter_oracle_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5);
int cosmos_nvme_pcie_adapter_oracle_rw_fields_supported(
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15);
int cosmos_nvme_pcie_adapter_oracle_flush_fields_supported(
    unsigned int dw6, unsigned int dw7, unsigned int dw8,
    unsigned int dw9, unsigned int dw10, unsigned int dw11,
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_oracle_transfer_bytes(
    unsigned int nlb, unsigned int block_bytes);
int cosmos_nvme_pcie_adapter_oracle_prp_span_valid(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_pcie_adapter_oracle_prp_first_bytes(
    unsigned int low1, unsigned int bytes);
unsigned int cosmos_nvme_pcie_adapter_oracle_io_kind(unsigned int opcode);
unsigned int cosmos_nvme_pcie_adapter_oracle_io_nlb(unsigned int dw12);
unsigned int cosmos_nvme_pcie_adapter_oracle_rw_control(unsigned int dw12);
int cosmos_nvme_pcie_adapter_oracle_rw_decode_valid(
    unsigned int common, unsigned int fields, unsigned int bytes,
    unsigned int prp);
unsigned int cosmos_nvme_pcie_adapter_oracle_write_zeroes_control(
    unsigned int dw12);
int cosmos_nvme_pcie_adapter_oracle_write_zeroes_fields_supported(
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2);
int cosmos_nvme_pcie_adapter_oracle_write_zeroes_decode_valid(
    unsigned int common, unsigned int fields);
int cosmos_nvme_pcie_adapter_oracle_dsm_fields_supported(
    unsigned int dw10, unsigned int dw12, unsigned int dw13,
    unsigned int dw14, unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_range_count(
    unsigned int dw10);
unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_attributes(
    unsigned int dw11);
unsigned int cosmos_nvme_pcie_adapter_oracle_dsm_data_bytes(
    unsigned int ranges);
int cosmos_nvme_pcie_adapter_oracle_dsm_decode_valid(
    unsigned int common, unsigned int fields, unsigned int prp);
int cosmos_nvme_pcie_adapter_oracle_flush_decode_valid(
    unsigned int common, unsigned int fields);
int cosmos_nvme_pcie_adapter_oracle_io_invalid_field(
    unsigned int kind, unsigned int valid);
int cosmos_nvme_pcie_adapter_oracle_admin_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5, unsigned int dw14,
    unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_oracle_admin_kind(unsigned int opcode);
unsigned int cosmos_nvme_pcie_adapter_oracle_admin_payload_bytes(
    unsigned int kind, unsigned int cdw10);
int cosmos_nvme_pcie_adapter_oracle_admin_transfer_valid(
    unsigned int kind, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes);
unsigned int cosmos_nvme_pcie_adapter_oracle_admin_invalid_field(
    unsigned int common, unsigned int transfer);
unsigned int cosmos_nvme_pcie_adapter_oracle_post_result(unsigned int result);
int cosmos_nvme_pcie_adapter_oracle_admin_payload_request_valid(
    unsigned int low1, unsigned int high1, unsigned int high2,
    unsigned int bytes);
unsigned int cosmos_nvme_pcie_adapter_oracle_admin_payload_result(int status);
int cosmos_nvme_pcie_adapter_oracle_no_async_result(void);
int cosmos_nvme_pcie_adapter_oracle_init_values_valid(
    unsigned int low, unsigned int high, unsigned int block_bytes);
int cosmos_nvme_pcie_adapter_oracle_frozen_selfcheck(void);

#endif
