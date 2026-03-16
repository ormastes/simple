/*
 * mmu.c — 64-bit MMU control register helpers for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/mm/mmu.h"

/* ── CR3: PML4 Base Register ──────────────────────────────────────── */

void mmu_load_pml4(uint64_t phys)
{
    __asm__ volatile ("movq %0, %%cr3" : : "r"(phys) : "memory");
}

uint64_t mmu_get_pml4(void)
{
    uint64_t val;
    __asm__ volatile ("movq %%cr3, %0" : "=r"(val));
    return val;
}

/* ── TLB management ────────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    uint64_t cr3;
    __asm__ volatile ("movq %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("movq %0, %%cr3" : : "r"(cr3) : "memory");
}

void mmu_invlpg(uint64_t addr)
{
    __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
}

/* ── CR0: Write Protect ───────────────────────────────────────────── */

void mmu_enable_write_protect(void)
{
    uint64_t cr0;
    __asm__ volatile ("movq %%cr0, %0" : "=r"(cr0));
    cr0 |= CR0_WP;
    __asm__ volatile ("movq %0, %%cr0" : : "r"(cr0) : "memory");
}

/* ── CR4: PGE ──────────────────────────────────────────────────────── */

void mmu_enable_pge(void)
{
    uint64_t cr4;
    __asm__ volatile ("movq %%cr4, %0" : "=r"(cr4));
    cr4 |= CR4_PGE;
    __asm__ volatile ("movq %0, %%cr4" : : "r"(cr4) : "memory");
}

/* ── EFER: NX and SYSCALL ──────────────────────────────────────────── */

void mmu_enable_nx(void)
{
    uint64_t efer = mmu_read_msr(MSR_EFER);
    efer |= EFER_NXE;
    mmu_write_msr(MSR_EFER, efer);
}

void mmu_enable_syscall(void)
{
    uint64_t efer = mmu_read_msr(MSR_EFER);
    efer |= EFER_SCE;
    mmu_write_msr(MSR_EFER, efer);
}

/* ── CR2: Fault Address ───────────────────────────────────────────── */

uint64_t mmu_get_fault_address(void)
{
    uint64_t val;
    __asm__ volatile ("movq %%cr2, %0" : "=r"(val));
    return val;
}

/* ── MSR Read/Write ───────────────────────────────────────────────── */

uint64_t mmu_read_msr(uint32_t msr)
{
    uint32_t lo, hi;
    __asm__ volatile ("rdmsr" : "=a"(lo), "=d"(hi) : "c"(msr));
    return ((uint64_t)hi << 32) | lo;
}

void mmu_write_msr(uint32_t msr, uint64_t val)
{
    uint32_t lo = (uint32_t)val;
    uint32_t hi = (uint32_t)(val >> 32);
    __asm__ volatile ("wrmsr" : : "c"(msr), "a"(lo), "d"(hi));
}
