#ifndef SIMPLE_COSMOS_NVME_PCIE_ADAPTER_POLICY_H
#define SIMPLE_COSMOS_NVME_PCIE_ADAPTER_POLICY_H

/* Stable, allocation-free scalar ABI exported by the pure-Simple owner. */
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_ABI_VERSION 1U
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_FUNCTIONS 34U
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_DECISIONS 45U
/* Compiler-emitted production sites; one named predicate has two locations. */
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_DECISION_SITES 46U
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_BRANCH_OUTCOMES 92U
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_HELPER_EXCLUSIONS 6U
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_OUTCOMES_0 0xFFFFFFFFU
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_OUTCOMES_1 0xFFFFFFFFU
#define COSMOS_NVME_PCIE_ADAPTER_POLICY_OUTCOMES_2 0x03FFFFFFU

#define COSMOS_NVME_PCIE_ADAPTER_IO_NONE 0U
#define COSMOS_NVME_PCIE_ADAPTER_IO_RW 1U
#define COSMOS_NVME_PCIE_ADAPTER_IO_FLUSH 2U
#define COSMOS_NVME_PCIE_ADAPTER_IO_WRITE_ZEROES 3U
#define COSMOS_NVME_PCIE_ADAPTER_IO_DSM 4U

#define COSMOS_NVME_PCIE_ADAPTER_ADMIN_NONE 0U
#define COSMOS_NVME_PCIE_ADAPTER_ADMIN_QUEUE 1U
#define COSMOS_NVME_PCIE_ADAPTER_ADMIN_IDENTIFY 2U
#define COSMOS_NVME_PCIE_ADAPTER_ADMIN_GET_LOG 3U

void cosmos_nvme_pcie_adapter_policy_coverage_reset(void);
unsigned int cosmos_nvme_pcie_adapter_policy_coverage_mask(
    unsigned int bank);
unsigned int cosmos_nvme_pcie_adapter_policy_coverage_required(
    unsigned int bank);
unsigned int cosmos_nvme_pcie_adapter_policy_coverage_decisions(void);
unsigned int cosmos_nvme_pcie_adapter_policy_function_count(void);
unsigned int cosmos_nvme_pcie_adapter_policy_command_cid(unsigned int dw0);
unsigned int cosmos_nvme_pcie_adapter_policy_command_opcode(unsigned int dw0);
int cosmos_nvme_pcie_adapter_policy_capacity_valid(
    unsigned int low, unsigned int high);
int cosmos_nvme_pcie_adapter_policy_block_bytes_valid(
    unsigned int block_bytes);
int cosmos_nvme_pcie_adapter_policy_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5);
int cosmos_nvme_pcie_adapter_policy_rw_fields_supported(
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15);
int cosmos_nvme_pcie_adapter_policy_flush_fields_supported(
    unsigned int dw6, unsigned int dw7, unsigned int dw8,
    unsigned int dw9, unsigned int dw10, unsigned int dw11,
    unsigned int dw12, unsigned int dw13, unsigned int dw14,
    unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_policy_transfer_bytes(
    unsigned int nlb, unsigned int block_bytes);
int cosmos_nvme_pcie_adapter_policy_prp_span_valid(
    unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_low, unsigned int prp2_high,
    unsigned int data_bytes);
unsigned int cosmos_nvme_pcie_adapter_policy_prp_first_bytes(
    unsigned int prp1_low, unsigned int payload_bytes);
unsigned int cosmos_nvme_pcie_adapter_policy_io_kind(unsigned int opcode);
unsigned int cosmos_nvme_pcie_adapter_policy_io_nlb(unsigned int dw12);
unsigned int cosmos_nvme_pcie_adapter_policy_rw_control(unsigned int dw12);
int cosmos_nvme_pcie_adapter_policy_rw_decode_valid(
    unsigned int common_supported, unsigned int fields_supported,
    unsigned int data_bytes, unsigned int prp_valid);
unsigned int cosmos_nvme_pcie_adapter_policy_write_zeroes_control(
    unsigned int dw12);
int cosmos_nvme_pcie_adapter_policy_write_zeroes_fields_supported(
    unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_low, unsigned int prp2_high);
int cosmos_nvme_pcie_adapter_policy_write_zeroes_decode_valid(
    unsigned int common_supported, unsigned int fields_supported);
int cosmos_nvme_pcie_adapter_policy_dsm_fields_supported(
    unsigned int dw10, unsigned int dw12, unsigned int dw13,
    unsigned int dw14, unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_policy_dsm_range_count(
    unsigned int dw10);
unsigned int cosmos_nvme_pcie_adapter_policy_dsm_attributes(
    unsigned int dw11);
unsigned int cosmos_nvme_pcie_adapter_policy_dsm_data_bytes(
    unsigned int range_count);
int cosmos_nvme_pcie_adapter_policy_dsm_decode_valid(
    unsigned int common_supported, unsigned int fields_supported,
    unsigned int prp_valid);
int cosmos_nvme_pcie_adapter_policy_flush_decode_valid(
    unsigned int common_supported, unsigned int fields_supported);
int cosmos_nvme_pcie_adapter_policy_io_invalid_field(
    unsigned int kind, unsigned int specific_valid);
int cosmos_nvme_pcie_adapter_policy_admin_common_fields_supported(
    unsigned int dw0, unsigned int dw2, unsigned int dw3,
    unsigned int dw4, unsigned int dw5, unsigned int dw14,
    unsigned int dw15);
unsigned int cosmos_nvme_pcie_adapter_policy_admin_kind(
    unsigned int opcode);
unsigned int cosmos_nvme_pcie_adapter_policy_admin_payload_bytes(
    unsigned int kind, unsigned int cdw10);
int cosmos_nvme_pcie_adapter_policy_admin_transfer_valid(
    unsigned int kind, unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_low, unsigned int prp2_high,
    unsigned int payload_bytes);
unsigned int cosmos_nvme_pcie_adapter_policy_admin_invalid_field(
    unsigned int common_supported, unsigned int transfer_valid);
unsigned int cosmos_nvme_pcie_adapter_policy_post_result(
    unsigned int result);
int cosmos_nvme_pcie_adapter_policy_admin_payload_request_valid(
    unsigned int prp1_low, unsigned int prp1_high,
    unsigned int prp2_high, unsigned int payload_bytes);
unsigned int cosmos_nvme_pcie_adapter_policy_admin_payload_result(int status);
int cosmos_nvme_pcie_adapter_policy_no_async_result(void);
int cosmos_nvme_pcie_adapter_policy_init_values_valid(
    unsigned int blocks_low, unsigned int blocks_high,
    unsigned int block_bytes);

#endif
