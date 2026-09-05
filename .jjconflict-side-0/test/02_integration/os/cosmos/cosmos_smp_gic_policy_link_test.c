#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include "../../../../src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic_policy.h"

unsigned int cosmos_contract_gic_limit_words(unsigned int words);
unsigned int cosmos_contract_smp_next_generation(unsigned int generation);
int cosmos_contract_smp_release_request_valid(
    unsigned int cpu_id, unsigned int entry, unsigned int stack_top);
unsigned int cosmos_contract_gic_quiesce_kind(
    unsigned int interrupt_id, int handler_result);

static void execute_all_decision_outcomes(void) {
    cosmos_smp_gic_policy_coverage_reset();
    (void)cosmos_gic_limit_words(0U);
    (void)cosmos_gic_limit_words(33U);
    (void)cosmos_gic_target_for_word(0U);
    (void)cosmos_gic_target_for_word(1U);
    (void)cosmos_smp_next_generation(0U);
    (void)cosmos_smp_next_generation(UINT_MAX);
    (void)cosmos_smp_release_request_valid(0U, 0x1000U, 0x2000U);
    (void)cosmos_smp_release_request_valid(1U, 0x1000U, 0x2000U);
    (void)cosmos_smp_release_request_valid(0U, 0U, 0x2000U);
    (void)cosmos_smp_release_request_valid(0U, 0x1000U, 0U);
    (void)cosmos_smp_release_request_valid(0U, 0x1002U, 0x2000U);
    (void)cosmos_smp_release_request_valid(0U, 0x1000U, 0x2004U);
    (void)cosmos_smp_secondary_state(0);
    (void)cosmos_smp_secondary_state(1);
    (void)cosmos_smp_ack_observed(3U, 7U, 7U);
    (void)cosmos_smp_ack_observed(2U, 7U, 7U);
    (void)cosmos_smp_ack_observed(3U, 6U, 7U);
    (void)cosmos_gic_pcie_irq_in_range(1U);
    (void)cosmos_gic_pcie_irq_in_range(2U);
    (void)cosmos_gic_quiesce_kind(61U, 0);
    (void)cosmos_gic_quiesce_kind(61U, 1);
    (void)cosmos_gic_quiesce_kind(7U, 4);
    (void)cosmos_gic_quiesce_kind(1020U, 4);
}

int main(void) {
    assert(cosmos_contract_gic_limit_words(32U) == 32U);
    assert(cosmos_contract_smp_next_generation(UINT_MAX) == 1U);
    assert(cosmos_contract_smp_release_request_valid(0U, 0x1000U, 0x2000U));
    assert(cosmos_contract_gic_quiesce_kind(61U, 1) == 2U);

    assert(cosmos_gic_words_from_typer(31U) == 32U);
    assert(cosmos_gic_irq_id(0xABCDE02AU) == 42U);
    assert(cosmos_gic_disable_offset(61U) == 0x184U);
    assert(cosmos_gic_disable_mask(61U) == 0x20000000U);
    assert(cosmos_gic_byte_shift(61U) == 8U);
    assert(cosmos_gic_config_shift(61U) == 26U);
    assert(cosmos_gic_priority_offset(61U) == 0x43CU);
    assert(cosmos_gic_target_offset(61U) == 0x83CU);
    assert(cosmos_gic_config_offset(61U) == 0xC0CU);
    assert(cosmos_gic_priority_value(0U, 61U) == 0x0000A000U);
    assert(cosmos_gic_target_cpu0_value(0U, 61U) == 0x00000100U);
    assert(cosmos_gic_level_config_value(UINT_MAX, 61U) == 0xF3FFFFFFU);

    execute_all_decision_outcomes();
    assert(cosmos_smp_gic_policy_coverage_decisions() == 17U);
    assert(cosmos_smp_gic_policy_coverage_required() == 0x3FFFFFFFFULL);
    assert(cosmos_smp_gic_policy_coverage_mask() ==
        cosmos_smp_gic_policy_coverage_required());
    puts("STATUS: PASS cosmos SMP/GIC mixed-object policy link");
    return 0;
}
