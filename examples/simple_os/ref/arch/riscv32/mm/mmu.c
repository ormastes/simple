/*
 * mmu.c — Sv32 MMU control for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/mm/mmu.h"

/* ── satp helpers ────────────────────────────────────────────────────── */

static inline uint32_t make_satp(uint32_t mode, uint32_t asid, uint32_t ppn)
{
    return mode | ((asid & 0x1FF) << 22) | (ppn & 0x003FFFFF);
}

/* ── Initialisation ──────────────────────────────────────────────────── */

void mmu_init(uint32_t root_page_table_phys)
{
    mmu_enable(root_page_table_phys);
}

/* ── Enable Sv32 paging ──────────────────────────────────────────────── */

void mmu_enable(uint32_t root_page_table_phys)
{
    /* PPN = physical address >> 12 */
    uint32_t ppn = root_page_table_phys >> 12;
    uint32_t satp = make_satp(SATP_MODE_SV32, 0, ppn);

    __asm__ volatile ("csrw satp, %0" : : "r"(satp) : "memory");

    /* Flush TLB after changing page table */
    mmu_flush_tlb();
}

/* ── Disable paging ──────────────────────────────────────────────────── */

void mmu_disable(void)
{
    __asm__ volatile ("csrw satp, zero" : : : "memory");
    mmu_flush_tlb();
}

/* ── Set page table with ASID ────────────────────────────────────────── */

void mmu_set_page_table(uint32_t root_phys, uint32_t asid)
{
    uint32_t ppn = root_phys >> 12;
    uint32_t satp = make_satp(SATP_MODE_SV32, asid, ppn);

    __asm__ volatile ("csrw satp, %0" : : "r"(satp) : "memory");
    mmu_flush_tlb();
}

/* ── TLB management ──────────────────────────────────────────────────── */

void mmu_flush_tlb(void)
{
    /* sfence.vma with rs1=x0, rs2=x0 flushes all TLB entries */
    __asm__ volatile ("sfence.vma zero, zero" : : : "memory");
}

void mmu_flush_tlb_page(uint32_t vaddr)
{
    __asm__ volatile ("sfence.vma %0, zero" : : "r"(vaddr) : "memory");
}

/* ── Read satp ───────────────────────────────────────────────────────── */

uint32_t mmu_get_satp(void)
{
    uint32_t val;
    __asm__ volatile ("csrr %0, satp" : "=r"(val));
    return val;
}
