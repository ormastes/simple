#ifndef SIMPLE_TEST_COSMOS_MMU_CACHE_POLICY_ORACLE_H
#define SIMPLE_TEST_COSMOS_MMU_CACHE_POLICY_ORACLE_H

unsigned int cosmos_mmu_cache_oracle_cache_way_shift(unsigned int ways);
unsigned int cosmos_mmu_cache_oracle_cache_setway_operand(
    unsigned int level, unsigned int way, unsigned int set,
    unsigned int line_shift, unsigned int way_shift);
unsigned int cosmos_mmu_cache_oracle_ttbr0_value(unsigned int table_address);
unsigned int cosmos_mmu_cache_oracle_sctlr_apply_policy(unsigned int current);
int cosmos_mmu_cache_oracle_sctlr_policy_valid(unsigned int value);
int cosmos_mmu_cache_oracle_control_registers_valid(
    unsigned int vbar, unsigned int expected_vbar,
    unsigned int ttbr0, unsigned int expected_ttbr0,
    unsigned int dacr, unsigned int sctlr);
int cosmos_mmu_cache_oracle_control_policy_contract(void);
unsigned int cosmos_mmu_cache_oracle_scu_invalidate_mask(unsigned int cpu_id);
int cosmos_mmu_cache_oracle_cache_enable_allowed(
    unsigned int scu_control, unsigned int actlr);
unsigned int cosmos_mmu_cache_oracle_section_descriptor(
    unsigned int base, unsigned int attributes);
unsigned int cosmos_mmu_cache_oracle_coarse_descriptor(
    unsigned int table_address);
unsigned int cosmos_mmu_cache_oracle_small_page_descriptor(unsigned int base);
unsigned int cosmos_mmu_cache_oracle_small_page_cached_rx_descriptor(
    unsigned int base);
unsigned int cosmos_mmu_cache_oracle_small_page_cached_rw_xn_descriptor(
    unsigned int base);
int cosmos_mmu_cache_oracle_l2_descriptor_executable(unsigned int descriptor);
int cosmos_mmu_cache_oracle_l2_descriptor_priv_writable(
    unsigned int descriptor);
int cosmos_mmu_cache_oracle_l2_descriptor_write_execute(
    unsigned int descriptor);
unsigned int cosmos_mmu_cache_oracle_firmware_l2_descriptor_for_address(
    unsigned int address, unsigned int rx_end);
int cosmos_mmu_cache_oracle_device_section(unsigned int section);
unsigned int cosmos_mmu_cache_oracle_l1_descriptor_for_address(
    unsigned int address, unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address);
unsigned int cosmos_mmu_cache_oracle_ocm_l2_descriptor_for_address(
    unsigned int address);
int cosmos_mmu_cache_oracle_mmu_poll_allowed(unsigned int poll);

#endif
