/*
 * mmu.c — ARMv7 MMU control for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/mm/mmu.h"

/* ── CP15 register access ──────────────────────────────────────────── */

/* Read SCTLR (System Control Register) */
static inline uint32_t read_sctlr(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c1, c0, 0" : "=r"(val));
    return val;
}

/* Write SCTLR */
static inline void write_sctlr(uint32_t val)
{
    __asm__ volatile ("mcr p15, 0, %0, c1, c0, 0" : : "r"(val) : "memory");
}

/* ── TTBR0 (Translation Table Base Register 0) ────────────────────── */

void mmu_set_ttbr0(uint32_t table_phys)
{
    /* TTBR0: set with inner/outer write-back write-allocate cacheable */
    uint32_t ttbr = table_phys | 0x6B;  /* IRGN=01, S=1, RGN=01, NOS=1 */
    __asm__ volatile ("mcr p15, 0, %0, c2, c0, 0" : : "r"(ttbr) : "memory");
}

uint32_t mmu_get_ttbr0(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c2, c0, 0" : "=r"(val));
    return val & 0xFFFFC000;  /* Mask off attribute bits */
}

/* ── TTBR1 ─────────────────────────────────────────────────────────── */

void mmu_set_ttbr1(uint32_t table_phys)
{
    uint32_t ttbr = table_phys | 0x6B;
    __asm__ volatile ("mcr p15, 0, %0, c2, c0, 1" : : "r"(ttbr) : "memory");
}

/* ── TTBCR (Translation Table Base Control) ────────────────────────── */

void mmu_set_ttbcr(uint32_t val)
{
    __asm__ volatile ("mcr p15, 0, %0, c2, c0, 2" : : "r"(val) : "memory");
}

/* ── DACR (Domain Access Control Register) ─────────────────────────── */

void mmu_set_dacr(uint32_t val)
{
    __asm__ volatile ("mcr p15, 0, %0, c3, c0, 0" : : "r"(val) : "memory");
}

/* ── TLB management ───────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    /* Invalidate entire unified TLB */
    __asm__ volatile (
        "dsb\n\t"
        "mcr p15, 0, %0, c8, c7, 0\n\t"  /* TLBIALL */
        "dsb\n\t"
        "isb\n\t"
        : : "r"(0) : "memory"
    );
}

void mmu_invalidate_tlb_entry(uint32_t vaddr)
{
    __asm__ volatile (
        "dsb\n\t"
        "mcr p15, 0, %0, c8, c7, 1\n\t"  /* TLBIMVA */
        "dsb\n\t"
        "isb\n\t"
        : : "r"(vaddr & ~0xFFF) : "memory"
    );
}

/* ── Cache maintenance ────────────────────────────────────────────── */

void mmu_invalidate_icache(void)
{
    __asm__ volatile (
        "mcr p15, 0, %0, c7, c5, 0\n\t"  /* ICIALLU */
        "isb\n\t"
        : : "r"(0) : "memory"
    );
}

void mmu_clean_dcache(void)
{
    /* Clean entire data cache by set/way — simplified single-level version */
    __asm__ volatile (
        "mcr p15, 0, %0, c7, c10, 0\n\t"  /* Clean entire D-cache */
        "dsb\n\t"
        : : "r"(0) : "memory"
    );
}

/* ── Barriers ──────────────────────────────────────────────────────── */

void mmu_dsb(void)
{
    __asm__ volatile ("dsb" ::: "memory");
}

void mmu_isb(void)
{
    __asm__ volatile ("isb" ::: "memory");
}

/* ── Enable / Disable MMU ──────────────────────────────────────────── */

void mmu_enable(void)
{
    uint32_t sctlr = read_sctlr();
    sctlr |= SCTLR_M;      /* Enable MMU */
    mmu_dsb();
    write_sctlr(sctlr);
    mmu_isb();
}

void mmu_disable(void)
{
    uint32_t sctlr = read_sctlr();
    sctlr &= ~SCTLR_M;     /* Disable MMU */
    write_sctlr(sctlr);
    mmu_dsb();
    mmu_isb();
}

/* ── Full MMU initialisation ───────────────────────────────────────── */

void mmu_init(void)
{
    /* Set TTBCR to use TTBR0 only (N=0) */
    mmu_set_ttbcr(0);

    /* Set all 16 domains to client mode */
    mmu_set_dacr(0x55555555);

    /* Flush TLB before enabling */
    mmu_flush_tlb();
}
