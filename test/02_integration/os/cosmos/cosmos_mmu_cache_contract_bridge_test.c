#include <assert.h>
#include <limits.h>

#include "cosmos_profile_openssd2_8ch8way_v300.h"

unsigned int cosmos_contract_cache_way_shift(unsigned int ways);
unsigned int cosmos_contract_cache_setway_operand(
    unsigned int level, unsigned int way, unsigned int set,
    unsigned int line_shift, unsigned int way_shift);
unsigned int cosmos_contract_ttbr0_value(unsigned int table_address);
unsigned int cosmos_contract_scu_invalidate_mask(unsigned int cpu_id);
int cosmos_contract_cache_enable_allowed(
    unsigned int scu_control, unsigned int actlr);
int cosmos_contract_mmu_poll_allowed(unsigned int poll);
int cosmos_contract_control_policy_selftest(void);
unsigned int cosmos_contract_l1_descriptor(
    unsigned int address, unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address);
unsigned int cosmos_contract_firmware_l2_descriptor(
    unsigned int address, unsigned int rx_end);
int cosmos_contract_l2_descriptor_executable(unsigned int descriptor);
int cosmos_contract_l2_descriptor_priv_writable(unsigned int descriptor);
int cosmos_contract_l2_descriptor_write_execute(unsigned int descriptor);
unsigned int cosmos_contract_ocm_l2_descriptor(unsigned int address);

int main(void) {
    unsigned int rx = cosmos_contract_firmware_l2_descriptor(
        0x00100000U, 0x00108000U);
    unsigned int rw = cosmos_contract_firmware_l2_descriptor(
        0x00108000U, 0x00108000U);

    assert(cosmos_contract_cache_way_shift(1U) == 0U);
    assert(cosmos_contract_cache_way_shift(4U) == 30U);
    assert(cosmos_contract_cache_setway_operand(
        1U, 3U, 127U, 5U, 30U) == 0xC0000FE2U);
    assert(cosmos_contract_ttbr0_value(0x12345678U) == 0x1234404AU);
    assert(cosmos_contract_scu_invalidate_mask(0U) == 0xFFFFU);
    assert(cosmos_contract_scu_invalidate_mask(1U) == 0U);
    assert(cosmos_contract_cache_enable_allowed(1U, 0x40U));
    assert(!cosmos_contract_cache_enable_allowed(0U, 0x40U));
    assert(cosmos_contract_mmu_poll_allowed(999999U));
    assert(!cosmos_contract_mmu_poll_allowed(1000000U));
    assert(!cosmos_contract_mmu_poll_allowed(UINT_MAX));
    assert(cosmos_contract_control_policy_selftest());
    assert(rx == 0x0010065EU);
    assert(rw == 0x0010845FU);
    assert(cosmos_contract_l2_descriptor_executable(rx));
    assert(!cosmos_contract_l2_descriptor_priv_writable(rx));
    assert(!cosmos_contract_l2_descriptor_write_execute(rx));
    assert(!cosmos_contract_l2_descriptor_executable(rw));
    assert(cosmos_contract_l2_descriptor_priv_writable(rw));
    assert(!cosmos_contract_l2_descriptor_write_execute(rw));
    assert(cosmos_contract_l1_descriptor(
        0x00200000U, 0x12345000U, 0x12345678U) == 0x00211412U);
    assert(cosmos_contract_l1_descriptor(
        0x18000000U, 0x12345000U, 0x12345678U) == 0x1801141EU);
    assert(cosmos_contract_l1_descriptor(
        0x43C00000U, 0x12345000U, 0x12345678U) == 0x43C10416U);
    assert(cosmos_contract_ocm_l2_descriptor(
        0xFFFC0000U) == 0xFFFC0453U);
    return 0;
}
