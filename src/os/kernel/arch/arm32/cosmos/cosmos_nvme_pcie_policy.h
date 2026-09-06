#ifndef SIMPLE_COSMOS_NVME_PCIE_POLICY_H
#define SIMPLE_COSMOS_NVME_PCIE_POLICY_H

/* Pure-Simple policy exports consumed only by the narrow C ABI bridge. */
int cosmos_nvme_pcie_policy_status_fields_valid(
    unsigned int sct, unsigned int sc, unsigned int dnr);
unsigned int cosmos_nvme_pcie_policy_status_word(
    unsigned int sct, unsigned int sc, unsigned int dnr);
int cosmos_nvme_pcie_policy_io_sq_valid(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high);
unsigned int cosmos_nvme_pcie_policy_io_sq_word1(
    unsigned int valid, unsigned int completion_queue_id,
    unsigned int entries, unsigned int address_high);
int cosmos_nvme_pcie_policy_io_cq_valid(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high);
unsigned int cosmos_nvme_pcie_policy_io_cq_word1(
    unsigned int valid, unsigned int irq_enable,
    unsigned int irq_vector, unsigned int entries,
    unsigned int address_high);

#endif
