/* Pointer-shaped C ABI publication for pure-Simple PCIe/NVMe queue policy. */
#include "cosmos_hal.h"
#include "cosmos_nvme_pcie_policy.h"
#include "cosmos_pcie_regs.h"

int cosmos_pcie_nvme_status_word(unsigned int sct, unsigned int sc,
                                 unsigned int dnr,
                                 unsigned int *status_word) {
    if (status_word == 0) {
        return COSMOS_INVALID;
    }
    if (!cosmos_nvme_pcie_policy_status_fields_valid(sct, sc, dnr)) {
        return COSMOS_INVALID;
    }
    *status_word = cosmos_nvme_pcie_policy_status_word(sct, sc, dnr);
    return COSMOS_OK;
}

int cosmos_pcie_nvme_io_sq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high,
    unsigned int *word0, unsigned int *word1) {
    if (word0 == 0) {
        return COSMOS_INVALID;
    }
    if (word1 == 0) {
        return COSMOS_INVALID;
    }
    if (!cosmos_nvme_pcie_policy_io_sq_valid(
            queue_id, valid, completion_queue_id, entries,
            address_low, address_high)) {
        return COSMOS_INVALID;
    }
    *word0 = address_low;
    *word1 = cosmos_nvme_pcie_policy_io_sq_word1(
        valid, completion_queue_id, entries, address_high);
    return COSMOS_OK;
}

int cosmos_pcie_nvme_io_cq_words(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high, unsigned int *word0,
    unsigned int *word1) {
    if (word0 == 0) {
        return COSMOS_INVALID;
    }
    if (word1 == 0) {
        return COSMOS_INVALID;
    }
    if (!cosmos_nvme_pcie_policy_io_cq_valid(
            queue_id, valid, irq_enable, irq_vector, entries,
            address_low, address_high)) {
        return COSMOS_INVALID;
    }
    *word0 = address_low;
    *word1 = cosmos_nvme_pcie_policy_io_cq_word1(
        valid, irq_enable, irq_vector, entries, address_high);
    return COSMOS_OK;
}
