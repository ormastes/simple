/* Frozen pre-migration C oracle for pure-Simple SMP/GIC scalar policy. */
#include "../../../../src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic_policy.h"

#define ORACLE_OK 0
#define ORACLE_POLL_LIMIT 1000000U
#define ORACLE_GIC_MAX_WORDS 32U
#define ORACLE_GIC_CPU0 0x01010101U
#define ORACLE_GIC_CPU0_TARGET 0x01U
#define ORACLE_GIC_PCI_PRIORITY 0xA0U
#define ORACLE_GIC_IRQ_ID_MASK 0x3FFU
#define ORACLE_GIC_SPURIOUS_MIN 1020U
#define ORACLE_PCIE_PL_IRQ_ID 61U
#define ORACLE_GICD_ICENABLER 0x180U
#define ORACLE_GICD_IPRIORITYR 0x400U
#define ORACLE_GICD_ITARGETSR 0x800U
#define ORACLE_GICD_ICFGR 0xC00U
#define ORACLE_SMP_READY 1U
#define ORACLE_SMP_ACKED 3U
#define ORACLE_SMP_CANCELLED 4U
#define ORACLE_GIC_QUIESCE_NONE 0U
#define ORACLE_GIC_QUIESCE_CPU 1U
#define ORACLE_GIC_QUIESCE_LINE 2U

unsigned int cosmos_gic_limit_words(unsigned int words) {
    return words != 0U && words <= ORACLE_GIC_MAX_WORDS ? words : 0U;
}

unsigned int cosmos_gic_words_from_typer(unsigned int typer) {
    return cosmos_gic_limit_words((typer & 0x1FU) + 1U);
}

unsigned int cosmos_gic_target_for_word(unsigned int word) {
    return word == 0U ? 0U : ORACLE_GIC_CPU0;
}

unsigned int cosmos_smp_next_generation(unsigned int generation) {
    generation++;
    return generation == 0U ? 1U : generation;
}

int cosmos_smp_release_request_valid(
    unsigned int cpu_id, unsigned int entry, unsigned int stack_top) {
    return cpu_id == 0U && entry != 0U && stack_top != 0U &&
        (entry & 3U) == 0U && (stack_top & 7U) == 0U;
}

int cosmos_smp_ready_observed(unsigned int state) {
    return state == ORACLE_SMP_READY;
}

unsigned int cosmos_smp_secondary_state(int result) {
    return result == ORACLE_OK ? ORACLE_SMP_ACKED : ORACLE_SMP_CANCELLED;
}

int cosmos_smp_ack_observed(
    unsigned int state, unsigned int ack, unsigned int generation) {
    return state == ORACLE_SMP_ACKED && ack == generation;
}

int cosmos_smp_poll_allowed(unsigned int poll) {
    return poll < ORACLE_POLL_LIMIT;
}

unsigned int cosmos_gic_irq_id(unsigned int acknowledge) {
    return acknowledge & ORACLE_GIC_IRQ_ID_MASK;
}

int cosmos_gic_irq_is_spurious(unsigned int interrupt_id) {
    return interrupt_id >= ORACLE_GIC_SPURIOUS_MIN;
}

unsigned int cosmos_gic_disable_offset(unsigned int interrupt_id) {
    return ORACLE_GICD_ICENABLER + (interrupt_id / 32U) * 4U;
}

unsigned int cosmos_gic_disable_mask(unsigned int interrupt_id) {
    return 1U << (interrupt_id & 31U);
}

unsigned int cosmos_gic_byte_shift(unsigned int interrupt_id) {
    return (interrupt_id & 3U) * 8U;
}

unsigned int cosmos_gic_config_shift(unsigned int interrupt_id) {
    return (interrupt_id & 15U) * 2U;
}

unsigned int cosmos_gic_priority_offset(unsigned int interrupt_id) {
    return ORACLE_GICD_IPRIORITYR + (interrupt_id / 4U) * 4U;
}

unsigned int cosmos_gic_target_offset(unsigned int interrupt_id) {
    return ORACLE_GICD_ITARGETSR + (interrupt_id / 4U) * 4U;
}

unsigned int cosmos_gic_config_offset(unsigned int interrupt_id) {
    return ORACLE_GICD_ICFGR + (interrupt_id / 16U) * 4U;
}

unsigned int cosmos_gic_priority_value(
    unsigned int current, unsigned int interrupt_id) {
    unsigned int shift = cosmos_gic_byte_shift(interrupt_id);
    unsigned int mask = 0xFFU << shift;
    return (current & ~mask) | (ORACLE_GIC_PCI_PRIORITY << shift);
}

unsigned int cosmos_gic_target_cpu0_value(
    unsigned int current, unsigned int interrupt_id) {
    unsigned int shift = cosmos_gic_byte_shift(interrupt_id);
    unsigned int mask = 0xFFU << shift;
    return (current & ~mask) | (ORACLE_GIC_CPU0_TARGET << shift);
}

unsigned int cosmos_gic_level_config_value(
    unsigned int current, unsigned int interrupt_id) {
    return current & ~(3U << cosmos_gic_config_shift(interrupt_id));
}

int cosmos_gic_pcie_irq_in_range(unsigned int words) {
    return cosmos_gic_limit_words(words) != 0U &&
        (ORACLE_PCIE_PL_IRQ_ID / 32U) < words;
}

int cosmos_gic_eoir_required(unsigned int interrupt_id) {
    return !cosmos_gic_irq_is_spurious(interrupt_id);
}

unsigned int cosmos_gic_quiesce_kind(
    unsigned int interrupt_id, int handler_result) {
    if (handler_result == ORACLE_OK || cosmos_gic_irq_is_spurious(interrupt_id)) {
        return ORACLE_GIC_QUIESCE_NONE;
    }
    return interrupt_id < 16U ?
        ORACLE_GIC_QUIESCE_CPU : ORACLE_GIC_QUIESCE_LINE;
}
