/*
 * mmu.c — AArch64 MMU control (SCTLR_EL1, TCR_EL1, MAIR_EL1, TTBR)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/mm/mmu.h"

/* ── Barrier helpers ───────────────────────────────────────────────── */

void mmu_dsb(void)
{
    __asm__ volatile ("dsb sy" ::: "memory");
}

void mmu_isb(void)
{
    __asm__ volatile ("isb" ::: "memory");
}

/* ── TTBR0 / TTBR1 ────────────────────────────────────────────────── */

void mmu_set_ttbr0(uint64_t phys)
{
    __asm__ volatile ("msr ttbr0_el1, %0" : : "r"(phys) : "memory");
    mmu_isb();
}

void mmu_set_ttbr1(uint64_t phys)
{
    __asm__ volatile ("msr ttbr1_el1, %0" : : "r"(phys) : "memory");
    mmu_isb();
}

uint64_t mmu_get_ttbr0(void)
{
    uint64_t val;
    __asm__ volatile ("mrs %0, ttbr0_el1" : "=r"(val));
    return val;
}

uint64_t mmu_get_ttbr1(void)
{
    uint64_t val;
    __asm__ volatile ("mrs %0, ttbr1_el1" : "=r"(val));
    return val;
}

/* ── TLB management ───────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    __asm__ volatile (
        "dsb ishst\n\t"
        "tlbi vmalle1is\n\t"
        "dsb ish\n\t"
        "isb"
        ::: "memory"
    );
}

void mmu_invalidate_addr(uint64_t vaddr)
{
    uint64_t page = vaddr >> 12;
    __asm__ volatile (
        "dsb ishst\n\t"
        "tlbi vale1is, %0\n\t"
        "dsb ish\n\t"
        "isb"
        : : "r"(page) : "memory"
    );
}

/* ── MMU enable / disable ──────────────────────────────────────────── */

void mmu_enable(void)
{
    uint64_t sctlr;
    __asm__ volatile ("mrs %0, sctlr_el1" : "=r"(sctlr));
    sctlr |= SCTLR_M | SCTLR_C | SCTLR_I;
    __asm__ volatile (
        "msr sctlr_el1, %0\n\t"
        "isb"
        : : "r"(sctlr) : "memory"
    );
}

void mmu_disable(void)
{
    uint64_t sctlr;
    __asm__ volatile ("mrs %0, sctlr_el1" : "=r"(sctlr));
    sctlr &= ~(uint64_t)(SCTLR_M | SCTLR_C | SCTLR_I);
    __asm__ volatile (
        "msr sctlr_el1, %0\n\t"
        "isb"
        : : "r"(sctlr) : "memory"
    );
}

/* ── Full MMU initialisation ───────────────────────────────────────── */

void mmu_init(void)
{
    /*
     * Configure MAIR_EL1:
     *   Attr0 = Device-nGnRnE (0x00)
     *   Attr1 = Normal Non-Cacheable (0x44)
     *   Attr2 = Normal WB-WA (0xFF)
     */
    uint64_t mair = ((uint64_t)MAIR_DEVICE_nGnRnE << (8 * MAIR_IDX_DEVICE))   |
                    ((uint64_t)MAIR_NORMAL_NC      << (8 * MAIR_IDX_NORMAL_NC)) |
                    ((uint64_t)MAIR_NORMAL_WB_WA   << (8 * MAIR_IDX_NORMAL));
    __asm__ volatile ("msr mair_el1, %0" : : "r"(mair));

    /*
     * Configure TCR_EL1:
     *   T0SZ = 25  (39-bit VA, 512 GB)
     *   TG0  = 4KB granule
     *   Cacheable, inner shareable for TTBR0 walks
     *   IPS  = 40-bit PA
     */
    uint64_t tcr = TCR_T0SZ(25)      |
                   TCR_TG0_4KB       |
                   TCR_SH0_INNER     |
                   TCR_ORGN0_WBWA    |
                   TCR_IRGN0_WBWA    |
                   TCR_IPS_40BIT;
    __asm__ volatile ("msr tcr_el1, %0" : : "r"(tcr));

    mmu_isb();
}
