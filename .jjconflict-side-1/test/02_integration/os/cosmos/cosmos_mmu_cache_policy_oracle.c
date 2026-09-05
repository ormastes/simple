/* Independent pre-migration C oracle for the 22 pure policy functions. */
#include "cosmos_mmu_cache_policy_oracle.h"

#define POLL_LIMIT 1000000U
#define SECTION_SIZE 0x00100000U
#define SMALL_PAGE_SIZE 0x00001000U
#define SECTION_MASK 0xFFF00000U
#define SMALL_PAGE_MASK 0xFFFFF000U
#define DDR_BASE 0x00100000U
#define DDR_END 0x3FFFFFFFU
#define FIRMWARE_BASE 0x00100000U
#define FIRMWARE_END 0x001FFFFFU
#define DMA_BASE 0x00200000U
#define DMA_END 0x17FFFFFFU
#define OCM_HIGH 0xFFFC0000U
#define SLCR_BASE 0xF8000000U
#define GIC_CPU_BASE 0xF8F00100U
#define NFC_BASE 0x43C00000U
#define PCIE_BASE 0x83C00000U

#define L1_COARSE 0x00000001U
#define L1_SECTION 0x00000002U
#define L1_B 0x00000004U
#define L1_C 0x00000008U
#define L1_XN 0x00000010U
#define L1_TEX1 0x00001000U
#define L1_AP_PRIV_RW 0x00000400U
#define L1_SHAREABLE 0x00010000U
#define L2_SMALL_PAGE 0x00000002U
#define L2_XN 0x00000001U
#define L2_B 0x00000004U
#define L2_C 0x00000008U
#define L2_AP_PRIV_RW 0x00000010U
#define L2_APX 0x00000200U
#define L2_AP_PRIV_RO (L2_AP_PRIV_RW | L2_APX)
#define L2_TEX1 0x00000040U
#define L2_SHAREABLE 0x00000400U
#define NORMAL_CACHED (L1_TEX1 | L1_C | L1_B | L1_SHAREABLE)
#define NORMAL_CACHED_XN (NORMAL_CACHED | L1_XN)
#define NORMAL_UNCACHED_XN (L1_TEX1 | L1_SHAREABLE | L1_XN)
#define DEVICE_XN (L1_B | L1_SHAREABLE | L1_XN)

#define SCTLR_M 0x00000001U
#define SCTLR_C 0x00000004U
#define SCTLR_I 0x00001000U
#define SCTLR_V 0x00002000U
#define SCTLR_TRE 0x10000000U
#define SCTLR_AFE 0x20000000U
#define SCTLR_SET (SCTLR_M | SCTLR_C | SCTLR_I)
#define SCTLR_CLEAR (SCTLR_V | SCTLR_TRE | SCTLR_AFE)
#define SCTLR_MASK (SCTLR_SET | SCTLR_CLEAR)
#define DACR_CLIENT 0x00000001U
#define ACTLR_SMP 0x00000040U
#define SCU_ENABLE 0x00000001U

unsigned int cosmos_mmu_cache_oracle_cache_way_shift(unsigned int ways) {
    return ways > 1U ? (unsigned int)__builtin_clz(ways - 1U) : 0U;
}

unsigned int cosmos_mmu_cache_oracle_cache_setway_operand(
    unsigned int level, unsigned int way, unsigned int set,
    unsigned int line_shift, unsigned int way_shift) {
    return (way << way_shift) | (set << line_shift) | (level << 1U);
}

unsigned int cosmos_mmu_cache_oracle_ttbr0_value(unsigned int table_address) {
    return (table_address & 0xFFFFC000U) | 0x40U | 0x02U | 0x08U;
}

unsigned int cosmos_mmu_cache_oracle_sctlr_apply_policy(unsigned int current) {
    return (current & ~SCTLR_MASK) | SCTLR_SET;
}

int cosmos_mmu_cache_oracle_sctlr_policy_valid(unsigned int value) {
    return (value & SCTLR_MASK) == SCTLR_SET;
}

int cosmos_mmu_cache_oracle_control_registers_valid(
    unsigned int vbar, unsigned int expected_vbar,
    unsigned int ttbr0, unsigned int expected_ttbr0,
    unsigned int dacr, unsigned int sctlr) {
    return vbar == expected_vbar && ttbr0 == expected_ttbr0 &&
        dacr == DACR_CLIENT &&
        cosmos_mmu_cache_oracle_sctlr_policy_valid(sctlr);
}

int cosmos_mmu_cache_oracle_control_policy_contract(void) {
    unsigned int configured =
        cosmos_mmu_cache_oracle_sctlr_apply_policy(0xFFFFFFFFU);
    unsigned int expected = (0xFFFFFFFFU & ~SCTLR_MASK) | SCTLR_SET;
    return cosmos_mmu_cache_oracle_sctlr_apply_policy(0U) == SCTLR_SET &&
        configured == expected &&
        cosmos_mmu_cache_oracle_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010404AU, 0x0010404AU, DACR_CLIENT, configured) &&
        !cosmos_mmu_cache_oracle_control_registers_valid(
            0x00100020U, 0x00100000U,
            0x0010404AU, 0x0010404AU, DACR_CLIENT, configured) &&
        !cosmos_mmu_cache_oracle_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010804AU, 0x0010404AU, DACR_CLIENT, configured) &&
        !cosmos_mmu_cache_oracle_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010404AU, 0x0010404AU, 0U, configured) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured & ~SCTLR_M) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured & ~SCTLR_C) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured & ~SCTLR_I) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured | SCTLR_V) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured | SCTLR_TRE) &&
        !cosmos_mmu_cache_oracle_sctlr_policy_valid(configured | SCTLR_AFE);
}

unsigned int cosmos_mmu_cache_oracle_scu_invalidate_mask(unsigned int cpu_id) {
    return cpu_id == 0U ? 0xFFFFU : 0U;
}

int cosmos_mmu_cache_oracle_cache_enable_allowed(
    unsigned int scu_control, unsigned int actlr) {
    return (scu_control & SCU_ENABLE) != 0U &&
        (actlr & ACTLR_SMP) != 0U;
}

unsigned int cosmos_mmu_cache_oracle_section_descriptor(
    unsigned int base, unsigned int attributes) {
    return (base & SECTION_MASK) | L1_SECTION | L1_AP_PRIV_RW | attributes;
}

unsigned int cosmos_mmu_cache_oracle_coarse_descriptor(
    unsigned int table_address) {
    return (table_address & 0xFFFFFC00U) | L1_COARSE;
}

unsigned int cosmos_mmu_cache_oracle_small_page_descriptor(unsigned int base) {
    return (base & SMALL_PAGE_MASK) | L2_SMALL_PAGE | L2_XN |
        L2_AP_PRIV_RW | L2_TEX1 | L2_SHAREABLE;
}

unsigned int cosmos_mmu_cache_oracle_small_page_cached_rx_descriptor(
    unsigned int base) {
    return (base & SMALL_PAGE_MASK) | L2_SMALL_PAGE | L2_AP_PRIV_RO |
        L2_TEX1 | L2_C | L2_B | L2_SHAREABLE;
}

unsigned int cosmos_mmu_cache_oracle_small_page_cached_rw_xn_descriptor(
    unsigned int base) {
    return (base & SMALL_PAGE_MASK) | L2_SMALL_PAGE | L2_XN |
        L2_AP_PRIV_RW | L2_TEX1 | L2_C | L2_B | L2_SHAREABLE;
}

int cosmos_mmu_cache_oracle_l2_descriptor_executable(unsigned int descriptor) {
    return (descriptor & L2_SMALL_PAGE) == L2_SMALL_PAGE &&
        (descriptor & L2_XN) == 0U;
}

int cosmos_mmu_cache_oracle_l2_descriptor_priv_writable(
    unsigned int descriptor) {
    return (descriptor & L2_SMALL_PAGE) == L2_SMALL_PAGE &&
        (descriptor & L2_AP_PRIV_RW) != 0U &&
        (descriptor & L2_APX) == 0U;
}

int cosmos_mmu_cache_oracle_l2_descriptor_write_execute(
    unsigned int descriptor) {
    return cosmos_mmu_cache_oracle_l2_descriptor_executable(descriptor) &&
        cosmos_mmu_cache_oracle_l2_descriptor_priv_writable(descriptor);
}

unsigned int cosmos_mmu_cache_oracle_firmware_l2_descriptor_for_address(
    unsigned int address, unsigned int rx_end) {
    unsigned int page = address & SMALL_PAGE_MASK;
    unsigned int rx_limit =
        (rx_end + SMALL_PAGE_SIZE - 1U) & SMALL_PAGE_MASK;
    if (page < FIRMWARE_BASE || page > FIRMWARE_END) {
        return 0U;
    }
    return page < rx_limit
        ? cosmos_mmu_cache_oracle_small_page_cached_rx_descriptor(page)
        : cosmos_mmu_cache_oracle_small_page_cached_rw_xn_descriptor(page);
}

int cosmos_mmu_cache_oracle_device_section(unsigned int section) {
    return section == (NFC_BASE & SECTION_MASK) ||
        section == (PCIE_BASE & SECTION_MASK) || section == 0xE0000000U ||
        section == (SLCR_BASE & SECTION_MASK) ||
        section == (GIC_CPU_BASE & SECTION_MASK);
}

unsigned int cosmos_mmu_cache_oracle_l1_descriptor_for_address(
    unsigned int address, unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address) {
    unsigned int section = address & SECTION_MASK;
    if (section == FIRMWARE_BASE) {
        return cosmos_mmu_cache_oracle_coarse_descriptor(
            firmware_l2_table_address);
    }
    if (section >= DDR_BASE && section <= DDR_END) {
        unsigned int attributes = section >= DMA_BASE && section <= DMA_END
            ? NORMAL_UNCACHED_XN : NORMAL_CACHED_XN;
        return cosmos_mmu_cache_oracle_section_descriptor(section, attributes);
    }
    if (cosmos_mmu_cache_oracle_device_section(section)) {
        return cosmos_mmu_cache_oracle_section_descriptor(section, DEVICE_XN);
    }
    if (section == (OCM_HIGH & SECTION_MASK)) {
        return cosmos_mmu_cache_oracle_coarse_descriptor(
            ocm_l2_table_address);
    }
    return 0U;
}

unsigned int cosmos_mmu_cache_oracle_ocm_l2_descriptor_for_address(
    unsigned int address) {
    unsigned int page = address & SMALL_PAGE_MASK;
    if ((page & SECTION_MASK) != (OCM_HIGH & SECTION_MASK) ||
        page < OCM_HIGH) {
        return 0U;
    }
    return cosmos_mmu_cache_oracle_small_page_descriptor(page);
}

int cosmos_mmu_cache_oracle_mmu_poll_allowed(unsigned int poll) {
    return poll < POLL_LIMIT;
}
