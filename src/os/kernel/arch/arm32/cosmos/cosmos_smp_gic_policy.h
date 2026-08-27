#ifndef SIMPLE_COSMOS_SMP_GIC_POLICY_H
#define SIMPLE_COSMOS_SMP_GIC_POLICY_H

/* Pure-Simple scalar policy exports. MMIO and assembly must not cross this ABI.
 * Coverage recording is dormant until the host evidence driver calls reset. */
void cosmos_smp_gic_policy_coverage_reset(void);
unsigned long long cosmos_smp_gic_policy_coverage_mask(void);
unsigned long long cosmos_smp_gic_policy_coverage_required(void);
unsigned int cosmos_smp_gic_policy_coverage_decisions(void);

unsigned int cosmos_gic_limit_words(unsigned int words);
unsigned int cosmos_gic_words_from_typer(unsigned int typer);
unsigned int cosmos_gic_target_for_word(unsigned int word);
unsigned int cosmos_smp_next_generation(unsigned int generation);
int cosmos_smp_release_request_valid(
    unsigned int cpu_id, unsigned int entry, unsigned int stack_top);
int cosmos_smp_ready_observed(unsigned int state);
unsigned int cosmos_smp_secondary_state(int result);
int cosmos_smp_ack_observed(
    unsigned int state, unsigned int ack, unsigned int generation);
int cosmos_smp_poll_allowed(unsigned int poll);
unsigned int cosmos_gic_irq_id(unsigned int acknowledge);
int cosmos_gic_irq_is_spurious(unsigned int interrupt_id);
unsigned int cosmos_gic_disable_offset(unsigned int interrupt_id);
unsigned int cosmos_gic_disable_mask(unsigned int interrupt_id);
unsigned int cosmos_gic_byte_shift(unsigned int interrupt_id);
unsigned int cosmos_gic_config_shift(unsigned int interrupt_id);
unsigned int cosmos_gic_priority_offset(unsigned int interrupt_id);
unsigned int cosmos_gic_target_offset(unsigned int interrupt_id);
unsigned int cosmos_gic_config_offset(unsigned int interrupt_id);
unsigned int cosmos_gic_priority_value(
    unsigned int current, unsigned int interrupt_id);
unsigned int cosmos_gic_target_cpu0_value(
    unsigned int current, unsigned int interrupt_id);
unsigned int cosmos_gic_level_config_value(
    unsigned int current, unsigned int interrupt_id);
int cosmos_gic_pcie_irq_in_range(unsigned int words);
int cosmos_gic_eoir_required(unsigned int interrupt_id);
unsigned int cosmos_gic_quiesce_kind(
    unsigned int interrupt_id, int handler_result);

#endif
