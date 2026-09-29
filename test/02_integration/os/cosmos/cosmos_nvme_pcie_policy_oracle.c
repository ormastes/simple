/* Independent C oracle frozen from the pre-migration queue/status policy. */
#include "cosmos_nvme_pcie_policy.h"

#define ORACLE_QUEUE_COUNT 8U

static int oracle_queue_base_valid(
    unsigned int valid, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    if (valid > 1U) {
        return 0;
    }
    if (valid == 0U) {
        return entries == 0U && address_low == 0U && address_high == 0U;
    }
    return entries != 0U && entries <= 256U &&
        (address_low & 0xFFFU) == 0U && address_high <= 0xFU &&
        (address_low != 0U || address_high != 0U);
}

int cosmos_nvme_pcie_policy_status_fields_valid(
    unsigned int sct, unsigned int sc, unsigned int dnr) {
    return sct <= 7U && sc <= 0xFFU && dnr <= 1U;
}

unsigned int cosmos_nvme_pcie_policy_status_word(
    unsigned int sct, unsigned int sc, unsigned int dnr) {
    return (sc << 1U) | (sct << 9U) | (dnr != 0U ? 0x8000U : 0U);
}

int cosmos_nvme_pcie_policy_io_sq_valid(
    unsigned int queue_id, unsigned int valid,
    unsigned int completion_queue_id, unsigned int entries,
    unsigned int address_low, unsigned int address_high) {
    return queue_id != 0U && queue_id <= ORACLE_QUEUE_COUNT &&
        oracle_queue_base_valid(valid, entries, address_low, address_high) &&
        ((valid != 0U && completion_queue_id != 0U &&
          completion_queue_id <= ORACLE_QUEUE_COUNT) ||
         (valid == 0U && completion_queue_id == 0U));
}

unsigned int cosmos_nvme_pcie_policy_io_sq_word1(
    unsigned int valid, unsigned int completion_queue_id,
    unsigned int entries, unsigned int address_high) {
    return address_high | (valid << 15U) |
        (completion_queue_id << 16U) |
        ((entries == 0U ? 0U : entries - 1U) << 24U);
}

int cosmos_nvme_pcie_policy_io_cq_valid(
    unsigned int queue_id, unsigned int valid,
    unsigned int irq_enable, unsigned int irq_vector,
    unsigned int entries, unsigned int address_low,
    unsigned int address_high) {
    return queue_id != 0U && queue_id <= ORACLE_QUEUE_COUNT &&
        oracle_queue_base_valid(valid, entries, address_low, address_high) &&
        irq_enable <= 1U && irq_vector <= 7U &&
        (valid != 0U || (irq_enable == 0U && irq_vector == 0U));
}

unsigned int cosmos_nvme_pcie_policy_io_cq_word1(
    unsigned int valid, unsigned int irq_enable,
    unsigned int irq_vector, unsigned int entries,
    unsigned int address_high) {
    return address_high | (valid << 15U) | (irq_vector << 16U) |
        (irq_enable << 19U) |
        ((entries == 0U ? 0U : entries - 1U) << 24U);
}
