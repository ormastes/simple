/* Cortex-A9 MMU, cache and PL310 bring-up for the Cosmos+ Zynq-7000 lane. */
#ifdef COSMOS_CONTRACT_TEST
#define COSMOS_POLL_LIMIT 1000000U
#define COSMOS_IS_QEMU 0
#define COSMOS_OCM_HIGH 0xFFFC0000U
#define COSMOS_SLCR_BASE 0xF8000000U
#define COSMOS_GIC_CPU_BASE 0xF8F00100U
#define COSMOS_GIC_DIST_BASE 0xF8F01000U
#define COSMOS_SCU_BASE 0xF8F00000U
#define COSMOS_PL310_BASE 0xF8F02000U
#define COSMOS_NFC_BASE 0x43C00000U
#define COSMOS_PCIE_BASE 0x83C00000U
#include "cosmos_profile_openssd2_8ch8way_v300.h"
#else
#include "cosmos_hal.h"
#if COSMOS_IS_QEMU
#define COSMOS_DDR_IDENTITY_BASE 0x00100000U
#define COSMOS_DDR_IDENTITY_END 0x3FFFFFFFU
#define COSMOS_FIRMWARE_IDENTITY_BASE 0x00100000U
#define COSMOS_FIRMWARE_IDENTITY_END 0x001FFFFFU
#define COSMOS_NFC_DMA_IDENTITY_BASE 0x00200000U
#define COSMOS_NFC_DMA_IDENTITY_END 0x17FFFFFFU
#define COSMOS_NFC_DATA_BUFFER_ADDRESS 0x10000000U
#define COSMOS_NFC_COMPLETE_FLAG_ADDRESS 0x17000000U
#define COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS 0x17000D00U
#define COSMOS_DDR_CACHED_RESUME_ADDRESS 0x18000000U
#endif
#endif

#define COSMOS_L1_ENTRIES             4096U
#define COSMOS_L2_ENTRIES              256U
#define COSMOS_SECTION_SIZE            0x00100000U
#define COSMOS_SMALL_PAGE_SIZE         0x00001000U
#define COSMOS_SECTION_MASK            0xFFF00000U
#define COSMOS_SMALL_PAGE_MASK         0xFFFFF000U

#define ARM_L1_COARSE                  0x00000001U
#define ARM_L1_SECTION                 0x00000002U
#define ARM_L1_B                       0x00000004U
#define ARM_L1_C                       0x00000008U
#define ARM_L1_XN                      0x00000010U
#define ARM_L1_TEX1                    0x00001000U
#define ARM_L1_AP_PRIV_RW              0x00000400U
#define ARM_L1_SHAREABLE               0x00010000U

#define ARM_L2_SMALL_PAGE              0x00000002U
#define ARM_L2_XN                      0x00000001U
#define ARM_L2_B                       0x00000004U
#define ARM_L2_C                       0x00000008U
#define ARM_L2_AP_PRIV_RW              0x00000010U
#define ARM_L2_APX                     0x00000200U
#define ARM_L2_AP_PRIV_RO              (ARM_L2_AP_PRIV_RW | ARM_L2_APX)
#define ARM_L2_TEX1                    0x00000040U
#define ARM_L2_SHAREABLE               0x00000400U

#define ARM_NORMAL_CACHED \
    (ARM_L1_TEX1 | ARM_L1_C | ARM_L1_B | ARM_L1_SHAREABLE)
#define ARM_NORMAL_CACHED_XN \
    (ARM_NORMAL_CACHED | ARM_L1_XN)
#define ARM_NORMAL_UNCACHED_XN \
    (ARM_L1_TEX1 | ARM_L1_SHAREABLE | ARM_L1_XN)
#define ARM_DEVICE_XN \
    (ARM_L1_B | ARM_L1_SHAREABLE | ARM_L1_XN)

#define ARM_SCTLR_M                    0x00000001U
#define ARM_SCTLR_C                    0x00000004U
#define ARM_SCTLR_I                    0x00001000U
#define ARM_SCTLR_V                    0x00002000U
#define ARM_SCTLR_TRE                  0x10000000U
#define ARM_SCTLR_AFE                  0x20000000U
#define ARM_SCTLR_POLICY_SET           (ARM_SCTLR_M | ARM_SCTLR_C | ARM_SCTLR_I)
#define ARM_SCTLR_POLICY_CLEAR         (ARM_SCTLR_V | ARM_SCTLR_TRE | ARM_SCTLR_AFE)
#define ARM_SCTLR_POLICY_MASK          (ARM_SCTLR_POLICY_SET | ARM_SCTLR_POLICY_CLEAR)

#define ARM_TTBR0_INNER_WB_WA          0x00000040U
#define ARM_TTBR0_SHAREABLE            0x00000002U
#define ARM_TTBR0_OUTER_WB_WA          0x00000008U
#define ARM_DACR_DOMAIN0_CLIENT        0x00000001U

#define ARM_ACTLR_SMP                   0x00000040U

#define SCU_CTRL                        0x000U
#define SCU_INVALIDATE_ALL              0x00CU
#define SCU_ENABLE                      0x00000001U

#define PL310_CTRL                     0x100U
#define PL310_CACHE_SYNC               0x730U
#define PL310_INV_WAY                  0x77CU
#define PL310_CLEAN_INV_WAY            0x7FCU
#define PL310_ALL_WAYS                 0x000000FFU

_Static_assert(ARM_TTBR0_INNER_WB_WA == 0x40U, "TTBR0 inner WBWA encoding");
_Static_assert(ARM_SCTLR_POLICY_SET == 0x00001005U, "SCTLR enable policy");
_Static_assert(ARM_SCTLR_POLICY_CLEAR == 0x30002000U, "SCTLR disable policy");
_Static_assert((ARM_SCTLR_POLICY_SET & ARM_SCTLR_POLICY_CLEAR) == 0U,
    "SCTLR policy masks must be disjoint");
_Static_assert(COSMOS_DDR_IDENTITY_BASE == 0x00100000U,
    "Cosmos+ DDR starts at 1 MiB");
_Static_assert(COSMOS_DDR_IDENTITY_END == 0x3FFFFFFFU,
    "Cosmos+ DDR ends at 1 GiB");
_Static_assert(COSMOS_FIRMWARE_IDENTITY_BASE == COSMOS_DDR_IDENTITY_BASE,
    "firmware must start with DDR");
_Static_assert(COSMOS_FIRMWARE_IDENTITY_END + 1U == COSMOS_NFC_DMA_IDENTITY_BASE,
    "firmware must end before DMA");
_Static_assert(COSMOS_NFC_DMA_IDENTITY_BASE == 0x00200000U,
    "official uncached window starts at 2 MiB");
_Static_assert(COSMOS_NFC_DATA_BUFFER_ADDRESS == 0x10000000U,
    "official NFC data buffer address");
_Static_assert(COSMOS_NFC_COMPLETE_FLAG_ADDRESS == 0x17000000U,
    "official NFC completion table address");
_Static_assert(COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS == 0x17000D00U,
    "official NFC temporary payload address");
_Static_assert(COSMOS_NFC_DMA_IDENTITY_END + 1U == COSMOS_DDR_CACHED_RESUME_ADDRESS,
    "cached DDR must resume after DMA");
_Static_assert(COSMOS_DDR_CACHED_RESUME_ADDRESS == 0x18000000U,
    "official cached DDR resume address");
_Static_assert((COSMOS_DDR_IDENTITY_BASE & (COSMOS_SECTION_SIZE - 1U)) == 0U &&
    ((COSMOS_DDR_IDENTITY_END + 1U) & (COSMOS_SECTION_SIZE - 1U)) == 0U &&
    (COSMOS_NFC_DMA_IDENTITY_BASE & (COSMOS_SECTION_SIZE - 1U)) == 0U &&
    ((COSMOS_NFC_DMA_IDENTITY_END + 1U) & (COSMOS_SECTION_SIZE - 1U)) == 0U,
    "Cosmos+ DDR and DMA bounds must be section aligned");

static unsigned int cosmos_cache_way_shift(unsigned int ways) {
    return ways > 1U ? (unsigned int)__builtin_clz(ways - 1U) : 0U;
}

static unsigned int cosmos_cache_setway_operand(
    unsigned int level,
    unsigned int way,
    unsigned int set,
    unsigned int line_shift,
    unsigned int way_shift
) {
    return (way << way_shift) |
        (set << line_shift) | (level << 1U);
}

static unsigned int cosmos_ttbr0_value(unsigned int table_address) {
    return (table_address & 0xFFFFC000U) |
        ARM_TTBR0_INNER_WB_WA | ARM_TTBR0_SHAREABLE | ARM_TTBR0_OUTER_WB_WA;
}

static unsigned int cosmos_sctlr_apply_policy(unsigned int current) {
    return (current & ~ARM_SCTLR_POLICY_MASK) | ARM_SCTLR_POLICY_SET;
}

static int cosmos_sctlr_policy_valid(unsigned int value) {
    return (value & ARM_SCTLR_POLICY_MASK) == ARM_SCTLR_POLICY_SET;
}

static int cosmos_control_registers_valid(
    unsigned int vbar,
    unsigned int expected_vbar,
    unsigned int ttbr0,
    unsigned int expected_ttbr0,
    unsigned int dacr,
    unsigned int sctlr
) {
    return vbar == expected_vbar &&
        ttbr0 == expected_ttbr0 &&
        dacr == ARM_DACR_DOMAIN0_CLIENT &&
        cosmos_sctlr_policy_valid(sctlr);
}

static int cosmos_control_policy_contract(void) {
    unsigned int configured = cosmos_sctlr_apply_policy(0xFFFFFFFFU);
    unsigned int expected =
        (0xFFFFFFFFU & ~ARM_SCTLR_POLICY_MASK) | ARM_SCTLR_POLICY_SET;

    return cosmos_sctlr_apply_policy(0U) == ARM_SCTLR_POLICY_SET &&
        configured == expected &&
        cosmos_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010404AU, 0x0010404AU,
            ARM_DACR_DOMAIN0_CLIENT, configured) &&
        !cosmos_control_registers_valid(
            0x00100020U, 0x00100000U,
            0x0010404AU, 0x0010404AU,
            ARM_DACR_DOMAIN0_CLIENT, configured) &&
        !cosmos_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010804AU, 0x0010404AU,
            ARM_DACR_DOMAIN0_CLIENT, configured) &&
        !cosmos_control_registers_valid(
            0x00100000U, 0x00100000U,
            0x0010404AU, 0x0010404AU,
            0U, configured) &&
        !cosmos_sctlr_policy_valid(configured & ~ARM_SCTLR_M) &&
        !cosmos_sctlr_policy_valid(configured & ~ARM_SCTLR_C) &&
        !cosmos_sctlr_policy_valid(configured & ~ARM_SCTLR_I) &&
        !cosmos_sctlr_policy_valid(configured | ARM_SCTLR_V) &&
        !cosmos_sctlr_policy_valid(configured | ARM_SCTLR_TRE) &&
        !cosmos_sctlr_policy_valid(configured | ARM_SCTLR_AFE);
}

static unsigned int cosmos_scu_invalidate_mask(unsigned int cpu_id) {
    return cpu_id == 0U ? 0xFFFFU : 0U;
}

static int cosmos_cache_enable_allowed(unsigned int scu_control, unsigned int actlr) {
    return (scu_control & SCU_ENABLE) != 0U && (actlr & ARM_ACTLR_SMP) != 0U;
}

static unsigned int cosmos_section_descriptor(
    unsigned int base,
    unsigned int attributes
) {
    return (base & COSMOS_SECTION_MASK) |
        ARM_L1_SECTION | ARM_L1_AP_PRIV_RW | attributes;
}

static unsigned int cosmos_coarse_descriptor(unsigned int table_address) {
    return (table_address & 0xFFFFFC00U) | ARM_L1_COARSE;
}

static unsigned int cosmos_small_page_descriptor(unsigned int base) {
    return (base & COSMOS_SMALL_PAGE_MASK) |
        ARM_L2_SMALL_PAGE | ARM_L2_XN | ARM_L2_AP_PRIV_RW |
        ARM_L2_TEX1 | ARM_L2_SHAREABLE;
}

static unsigned int cosmos_small_page_cached_rx_descriptor(unsigned int base) {
    return (base & COSMOS_SMALL_PAGE_MASK) |
        ARM_L2_SMALL_PAGE | ARM_L2_AP_PRIV_RO |
        ARM_L2_TEX1 | ARM_L2_C | ARM_L2_B | ARM_L2_SHAREABLE;
}

static unsigned int cosmos_small_page_cached_rw_xn_descriptor(unsigned int base) {
    return (base & COSMOS_SMALL_PAGE_MASK) |
        ARM_L2_SMALL_PAGE | ARM_L2_XN | ARM_L2_AP_PRIV_RW |
        ARM_L2_TEX1 | ARM_L2_C | ARM_L2_B | ARM_L2_SHAREABLE;
}

static int cosmos_l2_descriptor_executable(unsigned int descriptor) {
    return (descriptor & ARM_L2_SMALL_PAGE) == ARM_L2_SMALL_PAGE &&
        (descriptor & ARM_L2_XN) == 0U;
}

static int cosmos_l2_descriptor_priv_writable(unsigned int descriptor) {
    return (descriptor & ARM_L2_SMALL_PAGE) == ARM_L2_SMALL_PAGE &&
        (descriptor & ARM_L2_AP_PRIV_RW) != 0U &&
        (descriptor & ARM_L2_APX) == 0U;
}

static int cosmos_l2_descriptor_write_execute(unsigned int descriptor) {
    return cosmos_l2_descriptor_executable(descriptor) &&
        cosmos_l2_descriptor_priv_writable(descriptor);
}

static unsigned int cosmos_firmware_l2_descriptor_for_address(
    unsigned int address,
    unsigned int rx_end
) {
    unsigned int page = address & COSMOS_SMALL_PAGE_MASK;
    unsigned int rx_limit =
        (rx_end + COSMOS_SMALL_PAGE_SIZE - 1U) & COSMOS_SMALL_PAGE_MASK;

    if (page < COSMOS_FIRMWARE_IDENTITY_BASE ||
        page > COSMOS_FIRMWARE_IDENTITY_END) {
        return 0U;
    }
    return page < rx_limit
        ? cosmos_small_page_cached_rx_descriptor(page)
        : cosmos_small_page_cached_rw_xn_descriptor(page);
}

static int cosmos_device_section(unsigned int section) {
    return section == (COSMOS_NFC_BASE & COSMOS_SECTION_MASK) ||
        section == (COSMOS_PCIE_BASE & COSMOS_SECTION_MASK) ||
        section == 0xE0000000U ||
        section == (COSMOS_SLCR_BASE & COSMOS_SECTION_MASK) ||
        section == (COSMOS_GIC_CPU_BASE & COSMOS_SECTION_MASK);
}

static unsigned int cosmos_l1_descriptor_for_address(
    unsigned int address,
    unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address
) {
    unsigned int section = address & COSMOS_SECTION_MASK;

    if (section == COSMOS_FIRMWARE_IDENTITY_BASE) {
        return cosmos_coarse_descriptor(firmware_l2_table_address);
    }
    if (section >= COSMOS_DDR_IDENTITY_BASE &&
        section <= COSMOS_DDR_IDENTITY_END) {
        unsigned int attributes =
            section >= COSMOS_NFC_DMA_IDENTITY_BASE &&
            section <= COSMOS_NFC_DMA_IDENTITY_END
                ? ARM_NORMAL_UNCACHED_XN
                : ARM_NORMAL_CACHED_XN;
        return cosmos_section_descriptor(section, attributes);
    }
    if (cosmos_device_section(section)) {
        return cosmos_section_descriptor(section, ARM_DEVICE_XN);
    }
    if (section == (COSMOS_OCM_HIGH & COSMOS_SECTION_MASK)) {
        return cosmos_coarse_descriptor(ocm_l2_table_address);
    }
    return 0U;
}

static unsigned int cosmos_ocm_l2_descriptor_for_address(unsigned int address) {
    unsigned int page = address & COSMOS_SMALL_PAGE_MASK;

    if ((page & COSMOS_SECTION_MASK) !=
            (COSMOS_OCM_HIGH & COSMOS_SECTION_MASK) ||
        page < COSMOS_OCM_HIGH) {
        return 0U;
    }
    return cosmos_small_page_descriptor(page);
}

#if defined(COSMOS_CONTRACT_TEST) || !COSMOS_IS_QEMU
static int cosmos_mmu_poll_allowed(unsigned int poll) {
    return poll < COSMOS_POLL_LIMIT;
}
#endif

#ifdef COSMOS_CONTRACT_TEST
unsigned int cosmos_contract_cache_way_shift(unsigned int ways) {
    return cosmos_cache_way_shift(ways);
}

unsigned int cosmos_contract_cache_setway_operand(
    unsigned int level,
    unsigned int way,
    unsigned int set,
    unsigned int line_shift,
    unsigned int way_shift
) {
    return cosmos_cache_setway_operand(level, way, set, line_shift, way_shift);
}

unsigned int cosmos_contract_ttbr0_value(unsigned int table_address) {
    return cosmos_ttbr0_value(table_address);
}

unsigned int cosmos_contract_scu_invalidate_mask(unsigned int cpu_id) {
    return cosmos_scu_invalidate_mask(cpu_id);
}

int cosmos_contract_cache_enable_allowed(unsigned int scu_control, unsigned int actlr) {
    return cosmos_cache_enable_allowed(scu_control, actlr);
}

int cosmos_contract_mmu_poll_allowed(unsigned int poll) {
    return cosmos_mmu_poll_allowed(poll);
}

int cosmos_contract_control_policy_selftest(void) {
    return cosmos_control_policy_contract();
}

unsigned int cosmos_contract_l1_descriptor(
    unsigned int address,
    unsigned int firmware_l2_table_address,
    unsigned int ocm_l2_table_address
) {
    return cosmos_l1_descriptor_for_address(
        address, firmware_l2_table_address, ocm_l2_table_address);
}

unsigned int cosmos_contract_firmware_l2_descriptor(
    unsigned int address,
    unsigned int rx_end
) {
    return cosmos_firmware_l2_descriptor_for_address(address, rx_end);
}

int cosmos_contract_l2_descriptor_executable(unsigned int descriptor) {
    return cosmos_l2_descriptor_executable(descriptor);
}

int cosmos_contract_l2_descriptor_priv_writable(unsigned int descriptor) {
    return cosmos_l2_descriptor_priv_writable(descriptor);
}

int cosmos_contract_l2_descriptor_write_execute(unsigned int descriptor) {
    return cosmos_l2_descriptor_write_execute(descriptor);
}

unsigned int cosmos_contract_ocm_l2_descriptor(unsigned int address) {
    return cosmos_ocm_l2_descriptor_for_address(address);
}
#else
extern unsigned char _start[];
extern unsigned char __cosmos_rx_end[];

static unsigned int cosmos_l1_table[COSMOS_L1_ENTRIES]
    __attribute__((section(".mmu_table.l1"), aligned(16384)));
static unsigned int cosmos_firmware_l2_table[COSMOS_L2_ENTRIES]
    __attribute__((section(".mmu_table.firmware_l2"), aligned(1024)));
static unsigned int cosmos_ocm_l2_table[COSMOS_L2_ENTRIES]
    __attribute__((section(".mmu_table.ocm_l2"), aligned(1024)));
static unsigned int cosmos_l1_table_ready;

static unsigned int cosmos_read_sctlr(void) {
    unsigned int value;
    __asm__ volatile("mrc p15, 0, %0, c1, c0, 0" : "=r"(value));
    return value;
}

static void cosmos_write_sctlr(unsigned int value) {
    __asm__ volatile("mcr p15, 0, %0, c1, c0, 0" : : "r"(value) : "memory");
}

static unsigned int cosmos_read_actlr(void) {
    unsigned int value;
    __asm__ volatile("mrc p15, 0, %0, c1, c0, 1" : "=r"(value));
    return value;
}

static void cosmos_write_actlr(unsigned int value) {
    __asm__ volatile("mcr p15, 0, %0, c1, c0, 1" : : "r"(value) : "memory");
}

static void cosmos_write_ttbr0(unsigned int value) {
    __asm__ volatile("mcr p15, 0, %0, c2, c0, 0" : : "r"(value) : "memory");
}

static unsigned int cosmos_read_ttbr0(void) {
    unsigned int value;
    __asm__ volatile("mrc p15, 0, %0, c2, c0, 0" : "=r"(value));
    return value;
}

static void cosmos_write_ttbcr(unsigned int value) {
    __asm__ volatile("mcr p15, 0, %0, c2, c0, 2" : : "r"(value) : "memory");
}

static void cosmos_write_dacr(unsigned int value) {
    __asm__ volatile("mcr p15, 0, %0, c3, c0, 0" : : "r"(value) : "memory");
}

static unsigned int cosmos_read_dacr(void) {
    unsigned int value;
    __asm__ volatile("mrc p15, 0, %0, c3, c0, 0" : "=r"(value));
    return value;
}

static unsigned int cosmos_read_vbar(void) {
    unsigned int value;
    __asm__ volatile("mrc p15, 0, %0, c12, c0, 0" : "=r"(value));
    return value;
}

static void cosmos_invalidate_instruction_side(void) {
    unsigned int zero = 0U;
    __asm__ volatile("mcr p15, 0, %0, c7, c5, 0" : : "r"(zero) : "memory");
    __asm__ volatile("mcr p15, 0, %0, c7, c5, 6" : : "r"(zero) : "memory");
}

static void cosmos_invalidate_unified_tlb(void) {
    unsigned int zero = 0U;
    __asm__ volatile("mcr p15, 0, %0, c8, c7, 0" : : "r"(zero) : "memory");
}

static void cosmos_dcache_clean_invalidate_all(void) {
    unsigned int clidr;
    unsigned int level;
    unsigned int zero = 0U;

    __asm__ volatile("mrc p15, 1, %0, c0, c0, 1" : "=r"(clidr));
    for (level = 0U; level < ((clidr >> 24U) & 7U); level++) {
        unsigned int cache_type = (clidr >> (level * 3U)) & 7U;
        unsigned int ccsidr;
        unsigned int line_shift;
        unsigned int sets;
        unsigned int ways;
        unsigned int way_shift;
        unsigned int set;
        unsigned int way;

        if (cache_type < 2U || cache_type > 4U) {
            continue;
        }
        __asm__ volatile("mcr p15, 2, %0, c0, c0, 0" : : "r"(level << 1U) : "memory");
        cosmos_instruction_sync_barrier();
        __asm__ volatile("mrc p15, 1, %0, c0, c0, 0" : "=r"(ccsidr));
        line_shift = (ccsidr & 7U) + 4U;
        ways = ((ccsidr >> 3U) & 0x3FFU) + 1U;
        sets = ((ccsidr >> 13U) & 0x7FFFU) + 1U;
        way_shift = cosmos_cache_way_shift(ways);

        for (way = ways; way != 0U; way--) {
            for (set = sets; set != 0U; set--) {
                unsigned int setway = cosmos_cache_setway_operand(
                    level, way - 1U, set - 1U, line_shift, way_shift);
                __asm__ volatile("mcr p15, 0, %0, c7, c14, 2" : : "r"(setway) : "memory");
            }
        }
    }
    __asm__ volatile("mcr p15, 2, %0, c0, c0, 0" : : "r"(zero) : "memory");
    cosmos_data_sync_barrier();
}

static int cosmos_scu_enable_coherency(void) {
    unsigned int control;
    unsigned int actlr;
    unsigned int invalidate_mask = cosmos_scu_invalidate_mask(cosmos_cpu_id());

    if (invalidate_mask != 0U) {
        cosmos_mmio_write32(COSMOS_SCU_BASE + SCU_INVALIDATE_ALL, invalidate_mask);
        cosmos_data_sync_barrier();
    }
    control = cosmos_mmio_read32(COSMOS_SCU_BASE + SCU_CTRL);
    if ((control & SCU_ENABLE) == 0U) {
        cosmos_mmio_write32(COSMOS_SCU_BASE + SCU_CTRL, control | SCU_ENABLE);
        cosmos_data_sync_barrier();
    }
    if (!COSMOS_IS_QEMU &&
        !cosmos_cache_enable_allowed(
            cosmos_mmio_read32(COSMOS_SCU_BASE + SCU_CTRL), ARM_ACTLR_SMP)) {
        return COSMOS_HW_ERROR;
    }

    actlr = cosmos_read_actlr();
    cosmos_write_actlr(actlr | ARM_ACTLR_SMP);
    cosmos_data_sync_barrier();
    cosmos_instruction_sync_barrier();
    return COSMOS_IS_QEMU || cosmos_cache_enable_allowed(SCU_ENABLE, cosmos_read_actlr())
        ? COSMOS_OK : COSMOS_HW_ERROR;
}

static void cosmos_build_translation_table(void) {
    unsigned int index;
    unsigned int rx_end = (unsigned int)__cosmos_rx_end;

    for (index = 0U; index < COSMOS_L2_ENTRIES; index++) {
        cosmos_firmware_l2_table[index] = cosmos_firmware_l2_descriptor_for_address(
            COSMOS_FIRMWARE_IDENTITY_BASE + index * COSMOS_SMALL_PAGE_SIZE,
            rx_end);
        cosmos_ocm_l2_table[index] = cosmos_ocm_l2_descriptor_for_address(
            (COSMOS_OCM_HIGH & COSMOS_SECTION_MASK) +
                index * COSMOS_SMALL_PAGE_SIZE);
    }
    for (index = 0U; index < COSMOS_L1_ENTRIES; index++) {
        cosmos_l1_table[index] = cosmos_l1_descriptor_for_address(
            index * COSMOS_SECTION_SIZE,
            (unsigned int)cosmos_firmware_l2_table,
            (unsigned int)cosmos_ocm_l2_table);
    }
    cosmos_data_sync_barrier();
    cosmos_l1_table_ready = 1U;
}

#if !COSMOS_IS_QEMU
static int cosmos_pl310_wait_clear(unsigned int offset) {
    unsigned int poll;
    for (poll = 0U; cosmos_mmu_poll_allowed(poll); poll++) {
        if (cosmos_mmio_read32(COSMOS_PL310_BASE + offset) == 0U) {
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}
#endif

static int cosmos_pl310_init(void) {
#if COSMOS_IS_QEMU
    /* QEMU's zynq-a9 model does not expose a usable PL310 register block. */
    return COSMOS_OK;
#else
    unsigned int control = cosmos_mmio_read32(COSMOS_PL310_BASE + PL310_CTRL);
    unsigned int maintenance = (control & 1U) != 0U ? PL310_CLEAN_INV_WAY : PL310_INV_WAY;

    cosmos_mmio_write32(COSMOS_PL310_BASE + maintenance, PL310_ALL_WAYS);
    if (cosmos_pl310_wait_clear(maintenance) != COSMOS_OK) {
        return COSMOS_TIMEOUT;
    }
    cosmos_mmio_write32(COSMOS_PL310_BASE + PL310_CACHE_SYNC, 0U);
    cosmos_data_sync_barrier();
    if ((control & 1U) == 0U) {
        cosmos_mmio_write32(COSMOS_PL310_BASE + PL310_CTRL, 1U);
        cosmos_data_sync_barrier();
        if ((cosmos_mmio_read32(COSMOS_PL310_BASE + PL310_CTRL) & 1U) == 0U) {
            return COSMOS_HW_ERROR;
        }
    }
    return COSMOS_OK;
#endif
}

int cosmos_mmu_cache_selftest(void) {
    unsigned int firmware;
    unsigned int dma;
    unsigned int cached_resume;
    unsigned int ddr_end;
    unsigned int nfc;
    unsigned int pcie;
    unsigned int ocm;
    unsigned int firmware_l2_address = (unsigned int)cosmos_firmware_l2_table;
    unsigned int ocm_l2_address = (unsigned int)cosmos_ocm_l2_table;
    unsigned int rx_end = (unsigned int)__cosmos_rx_end;
    unsigned int rx_last_index =
        ((rx_end - 1U) & ~COSMOS_SECTION_MASK) / COSMOS_SMALL_PAGE_SIZE;
    unsigned int rw_first_index =
        (rx_end & ~COSMOS_SECTION_MASK) / COSMOS_SMALL_PAGE_SIZE;
    unsigned int ocm_first_page =
        (COSMOS_OCM_HIGH & ~COSMOS_SECTION_MASK) / COSMOS_SMALL_PAGE_SIZE;

    if (cosmos_l1_table_ready == 0U) {
        cosmos_build_translation_table();
    }
    firmware = cosmos_l1_table[COSMOS_FIRMWARE_IDENTITY_BASE >> 20U];
    dma = cosmos_l1_table[COSMOS_NFC_DMA_IDENTITY_BASE >> 20U];
    cached_resume =
        cosmos_l1_table[COSMOS_DDR_CACHED_RESUME_ADDRESS >> 20U];
    ddr_end = cosmos_l1_table[COSMOS_DDR_IDENTITY_END >> 20U];
    nfc = cosmos_l1_table[COSMOS_NFC_BASE >> 20U];
    pcie = cosmos_l1_table[COSMOS_PCIE_BASE >> 20U];
    ocm = cosmos_l1_table[COSMOS_OCM_HIGH >> 20U];
    if (!cosmos_control_policy_contract() ||
        cosmos_cache_way_shift(1U) != 0U ||
        cosmos_cache_way_shift(2U) != 31U ||
        cosmos_cache_way_shift(4U) != 30U ||
        cosmos_cache_way_shift(8U) != 29U ||
        ARM_TTBR0_INNER_WB_WA != 0x40U ||
        cosmos_l1_table[0U] != 0U ||
        rx_end <= COSMOS_FIRMWARE_IDENTITY_BASE ||
        rx_end >= COSMOS_NFC_DMA_IDENTITY_BASE ||
        firmware != cosmos_coarse_descriptor(firmware_l2_address) ||
        cosmos_firmware_l2_table[0U] !=
            cosmos_small_page_cached_rx_descriptor(COSMOS_FIRMWARE_IDENTITY_BASE) ||
        cosmos_firmware_l2_table[rx_last_index] !=
            cosmos_small_page_cached_rx_descriptor(
                (rx_end - 1U) & COSMOS_SMALL_PAGE_MASK) ||
        cosmos_firmware_l2_table[rw_first_index] !=
            cosmos_small_page_cached_rw_xn_descriptor(
                rx_end & COSMOS_SMALL_PAGE_MASK) ||
        cosmos_firmware_l2_table[COSMOS_L2_ENTRIES - 1U] !=
            cosmos_small_page_cached_rw_xn_descriptor(COSMOS_FIRMWARE_IDENTITY_END) ||
        cosmos_l2_descriptor_write_execute(cosmos_firmware_l2_table[0U]) ||
        cosmos_l2_descriptor_write_execute(cosmos_firmware_l2_table[rw_first_index]) ||
        dma != cosmos_section_descriptor(
            COSMOS_NFC_DMA_IDENTITY_BASE, ARM_NORMAL_UNCACHED_XN) ||
        cosmos_l1_table[COSMOS_NFC_DATA_BUFFER_ADDRESS >> 20U] !=
            cosmos_section_descriptor(
                COSMOS_NFC_DATA_BUFFER_ADDRESS, ARM_NORMAL_UNCACHED_XN) ||
        cosmos_l1_table[COSMOS_NFC_COMPLETE_FLAG_ADDRESS >> 20U] !=
            cosmos_section_descriptor(
                COSMOS_NFC_COMPLETE_FLAG_ADDRESS, ARM_NORMAL_UNCACHED_XN) ||
        cosmos_l1_table[COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS >> 20U] !=
            cosmos_section_descriptor(
                COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS, ARM_NORMAL_UNCACHED_XN) ||
        cached_resume != cosmos_section_descriptor(
            COSMOS_DDR_CACHED_RESUME_ADDRESS, ARM_NORMAL_CACHED_XN) ||
        ddr_end != cosmos_section_descriptor(
            COSMOS_DDR_IDENTITY_END, ARM_NORMAL_CACHED_XN) ||
        cosmos_l1_table[0x400U] != 0U ||
        nfc != cosmos_section_descriptor(COSMOS_NFC_BASE, ARM_DEVICE_XN) ||
        pcie != cosmos_section_descriptor(COSMOS_PCIE_BASE, ARM_DEVICE_XN) ||
        cosmos_l1_table[0xE00U] !=
            cosmos_section_descriptor(0xE0000000U, ARM_DEVICE_XN) ||
        cosmos_l1_table[COSMOS_SLCR_BASE >> 20U] !=
            cosmos_section_descriptor(COSMOS_SLCR_BASE, ARM_DEVICE_XN) ||
        cosmos_l1_table[COSMOS_GIC_CPU_BASE >> 20U] !=
            cosmos_section_descriptor(COSMOS_GIC_CPU_BASE, ARM_DEVICE_XN) ||
        ocm != cosmos_coarse_descriptor(ocm_l2_address) ||
        cosmos_ocm_l2_table[ocm_first_page - 1U] != 0U ||
        cosmos_ocm_l2_table[ocm_first_page] !=
            cosmos_small_page_descriptor(COSMOS_OCM_HIGH) ||
        cosmos_ocm_l2_table[COSMOS_L2_ENTRIES - 1U] !=
            cosmos_small_page_descriptor(0xFFFFF000U) ||
        cosmos_l1_table[0x700U] != 0U) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}

int cosmos_mmu_cache_init(void) {
    unsigned int sctlr;
    unsigned int ttbr0;

    if (cosmos_l1_table_ready == 0U) {
        cosmos_build_translation_table();
    }
    if (cosmos_mmu_cache_selftest() != COSMOS_OK) {
        return COSMOS_INVALID;
    }
    if (cosmos_scu_enable_coherency() != COSMOS_OK) {
        return COSMOS_HW_ERROR;
    }

    cosmos_dcache_clean_invalidate_all();
    if (cosmos_cpu_id() == 0U && cosmos_pl310_init() != COSMOS_OK) {
        return COSMOS_TIMEOUT;
    }

    ttbr0 = cosmos_ttbr0_value((unsigned int)cosmos_l1_table);
    cosmos_data_sync_barrier();
    cosmos_write_ttbcr(0U);
    cosmos_write_ttbr0(ttbr0);
    cosmos_write_dacr(ARM_DACR_DOMAIN0_CLIENT);
    cosmos_data_sync_barrier();
    cosmos_invalidate_unified_tlb();
    cosmos_invalidate_instruction_side();
    cosmos_data_sync_barrier();
    cosmos_instruction_sync_barrier();

    sctlr = cosmos_sctlr_apply_policy(cosmos_read_sctlr());
    cosmos_data_sync_barrier();
    cosmos_write_sctlr(sctlr);
    cosmos_instruction_sync_barrier();
    if (!cosmos_control_registers_valid(
            cosmos_read_vbar(), (unsigned int)_start,
            cosmos_read_ttbr0(), ttbr0,
            cosmos_read_dacr(), cosmos_read_sctlr())) {
        return COSMOS_HW_ERROR;
    }
    return COSMOS_OK;
}
#endif
