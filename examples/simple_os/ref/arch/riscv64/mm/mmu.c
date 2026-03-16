/*
 * mmu.c — Sv39 MMU control for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/mm/mmu.h"

/* ── Initialisation ───────────────────────────────────────────────── */

void mmu_init(void)
{
    /* Start with paging disabled (Bare mode) */
    mmu_disable();
    mmu_flush_tlb();
}

/* ── Enable Sv39 paging ───────────────────────────────────────────── */

void mmu_enable(uint64_t root_page_table_phys, uint16_t asid)
{
    uint64_t ppn = root_page_table_phys >> 12;
    uint64_t satp = SATP_VALUE(SATP_MODE_SV39, asid, ppn);

    __asm__ volatile (
        "csrw satp, %0\n"
        "sfence.vma zero, zero\n"
        : : "r"(satp) : "memory"
    );
}

/* ── Disable paging ───────────────────────────────────────────────── */

void mmu_disable(void)
{
    __asm__ volatile (
        "csrw satp, zero\n"
        "sfence.vma zero, zero\n"
        : : : "memory"
    );
}

/* ── Set page table without mode change ───────────────────────────── */

void mmu_set_page_table(uint64_t root_page_table_phys, uint16_t asid)
{
    mmu_enable(root_page_table_phys, asid);
}

/* ── TLB management ───────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    __asm__ volatile ("sfence.vma zero, zero" : : : "memory");
}

void mmu_flush_tlb_page(uint64_t vaddr)
{
    __asm__ volatile ("sfence.vma %0, zero" : : "r"(vaddr) : "memory");
}

void mmu_flush_tlb_asid(uint16_t asid)
{
    __asm__ volatile ("sfence.vma zero, %0" : : "r"((uint64_t)asid) : "memory");
}

/* ── satp read ────────────────────────────────────────────────────── */

uint64_t mmu_get_satp(void)
{
    uint64_t val;
    __asm__ volatile ("csrr %0, satp" : "=r"(val));
    return val;
}
