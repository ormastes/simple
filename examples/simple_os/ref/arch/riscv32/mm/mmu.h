/*
 * mmu.h — Sv32 MMU control for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Sv32 uses the satp CSR:
 *   Bit 31:    MODE (0=Bare, 1=Sv32)
 *   Bits 30-22: ASID (9 bits)
 *   Bits 21-0:  PPN (22 bits — physical page number of root table)
 */

#ifndef ARCH_RISCV32_MM_MMU_H
#define ARCH_RISCV32_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── satp MODE field ─────────────────────────────────────────────────── */

#define SATP_MODE_BARE  0x00000000
#define SATP_MODE_SV32  0x80000000

/* ── Public API ──────────────────────────────────────────────────────── */

/* Initialise the MMU (called after page tables are set up) */
void     mmu_init(uint32_t root_page_table_phys);

/* Enable Sv32 paging */
void     mmu_enable(uint32_t root_page_table_phys);

/* Disable paging (bare mode) */
void     mmu_disable(void);

/* Set the root page table (writes satp) */
void     mmu_set_page_table(uint32_t root_phys, uint32_t asid);

/* Flush the entire TLB */
void     mmu_flush_tlb(void);

/* Flush a single TLB entry */
void     mmu_flush_tlb_page(uint32_t vaddr);

/* Read the current satp value */
uint32_t mmu_get_satp(void);

#endif /* ARCH_RISCV32_MM_MMU_H */
