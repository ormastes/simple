#ifndef SIMPLE_COSMOS_PCIE_RESIDUAL_POLICY_H
#define SIMPLE_COSMOS_PCIE_RESIDUAL_POLICY_H

/* Allocation-free scalar ABI owned by cosmos_pcie_residual_policy.spl. */
void cosmos_pcie_residual_policy_coverage_reset(void);
unsigned int cosmos_pcie_residual_policy_coverage_mask(unsigned int bank);
unsigned int cosmos_pcie_residual_policy_coverage_required(unsigned int bank);
unsigned int cosmos_pcie_residual_policy_coverage_decisions(void);
unsigned int cosmos_pcie_residual_policy_function_count(void);

int cosmos_pcie_residual_policy_snapshot_status(
    unsigned int status, unsigned int function,
    unsigned int nvme, unsigned int admin);
int cosmos_pcie_residual_policy_snapshots_equal(
    unsigned int left_status, unsigned int left_function,
    unsigned int left_nvme, unsigned int left_admin,
    unsigned int right_status, unsigned int right_function,
    unsigned int right_nvme, unsigned int right_admin);
int cosmos_pcie_residual_policy_nvme_cmd_word_status(unsigned int word);
int cosmos_pcie_residual_policy_nvme_completion_fields_valid(
    unsigned int queue_id, unsigned int slot_tag,
    unsigned int sequence, unsigned int cid,
    unsigned int status_word);
int cosmos_pcie_residual_policy_host_dma_device_buffer_status(
    unsigned int device_address, unsigned int length);
int cosmos_pcie_residual_policy_host_dma_direct_status(
    unsigned int device_address, unsigned int host_address_high,
    unsigned int host_address_low, unsigned int length);
unsigned int cosmos_pcie_residual_policy_host_dma_counter_shift(
    unsigned int direct, unsigned int direction);
unsigned int cosmos_pcie_residual_policy_host_dma_counter_index(
    unsigned int direct, unsigned int direction);
unsigned int cosmos_pcie_residual_policy_host_dma_direct_word3(
    unsigned int direction, unsigned int length);
int cosmos_pcie_residual_policy_host_dma_auto_status(
    unsigned int command_slot_tag, unsigned int command_4k_offset,
    unsigned int device_address);
unsigned int cosmos_pcie_residual_policy_host_dma_auto_word3(
    unsigned int direction, unsigned int command_slot_tag,
    unsigned int command_4k_offset);
unsigned int cosmos_pcie_residual_policy_nvme_completion_word2(
    unsigned int slot_tag, unsigned int status_word);

#endif
