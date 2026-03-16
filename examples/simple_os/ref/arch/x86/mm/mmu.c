/*
 * mmu.c — MMU control register helpers for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86/mm/mmu.h"

/* ── CR3: Page Directory Base Register ─────────────────────────────── */

void mmu_load_page_directory(uint32_t phys)
{
    __asm__ volatile ("movl %0, %%cr3" : : "r"(phys) : "memory");
}

uint32_t mmu_get_page_directory(void)
{
    uint32_t val;
    __asm__ volatile ("movl %%cr3, %0" : "=r"(val));
    return val;
}

/* ── CR0: Paging and Write Protect ─────────────────────────────────── */

void mmu_enable_paging(void)
{
    uint32_t cr0;
    __asm__ volatile ("movl %%cr0, %0" : "=r"(cr0));
    cr0 |= CR0_PG;
    __asm__ volatile ("movl %0, %%cr0" : : "r"(cr0) : "memory");
}

void mmu_disable_paging(void)
{
    uint32_t cr0;
    __asm__ volatile ("movl %%cr0, %0" : "=r"(cr0));
    cr0 &= ~CR0_PG;
    __asm__ volatile ("movl %0, %%cr0" : : "r"(cr0) : "memory");
}

void mmu_enable_write_protect(void)
{
    uint32_t cr0;
    __asm__ volatile ("movl %%cr0, %0" : "=r"(cr0));
    cr0 |= CR0_WP;
    __asm__ volatile ("movl %0, %%cr0" : : "r"(cr0) : "memory");
}

/* ── TLB management ────────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    uint32_t cr3;
    __asm__ volatile ("movl %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("movl %0, %%cr3" : : "r"(cr3) : "memory");
}

void mmu_invlpg(uint32_t addr)
{
    __asm__ volatile ("invlpg (%0)" : : "r"(addr) : "memory");
}

/* ── CR4: PSE and PGE ──────────────────────────────────────────────── */

void mmu_enable_pse(void)
{
    uint32_t cr4;
    __asm__ volatile ("movl %%cr4, %0" : "=r"(cr4));
    cr4 |= CR4_PSE;
    __asm__ volatile ("movl %0, %%cr4" : : "r"(cr4) : "memory");
}

void mmu_enable_pge(void)
{
    uint32_t cr4;
    __asm__ volatile ("movl %%cr4, %0" : "=r"(cr4));
    cr4 |= CR4_PGE;
    __asm__ volatile ("movl %0, %%cr4" : : "r"(cr4) : "memory");
}

/* ── CR2: Fault Address ────────────────────────────────────────────── */

uint32_t mmu_get_fault_address(void)
{
    uint32_t val;
    __asm__ volatile ("movl %%cr2, %0" : "=r"(val));
    return val;
}
