/*
 * mmu.h — Sv39 MMU control for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Sv39: 3-level page tables, 39-bit virtual address space.
 *
 * satp register format (RV64):
 *   MODE (bits 63:60) = 8 for Sv39
 *   ASID (bits 59:44) = address space identifier
 *   PPN  (bits 43:0)  = physical page number of root page table
 */

#ifndef ARCH_RISCV64_MM_MMU_H
#define ARCH_RISCV64_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── satp MODE values ─────────────────────────────────────────────── */

#define SATP_MODE_BARE  0UL
#define SATP_MODE_SV39  8UL
#define SATP_MODE_SV48  9UL

/* ── satp field positions ─────────────────────────────────────────── */

#define SATP_MODE_SHIFT 60
#define SATP_ASID_SHIFT 44
#define SATP_PPN_MASK   0x00000FFFFFFFFFFFUL

/* ── Build a satp value ───────────────────────────────────────────── */

#define SATP_VALUE(mode, asid, ppn) \
    (((mode) << SATP_MODE_SHIFT) | \
     ((uint64_t)(asid) << SATP_ASID_SHIFT) | \
     ((ppn) & SATP_PPN_MASK))

/* ── mstatus bits ─────────────────────────────────────────────────── */

#define MSTATUS_MIE     (1UL << 3)      /* Machine Interrupt Enable  */
#define MSTATUS_SIE     (1UL << 1)      /* Supervisor Interrupt Enable */
#define MSTATUS_MPIE    (1UL << 7)      /* Previous MIE              */
#define MSTATUS_MPP_M   (3UL << 11)     /* MPP = Machine mode        */
#define MSTATUS_MPP_S   (1UL << 11)     /* MPP = Supervisor mode     */
#define MSTATUS_MPP_U   (0UL << 11)     /* MPP = User mode           */

/* ── Public API ───────────────────────────────────────────────────── */

void     mmu_init(void);
void     mmu_enable(uint64_t root_page_table_phys, uint16_t asid);
void     mmu_disable(void);
void     mmu_set_page_table(uint64_t root_page_table_phys, uint16_t asid);
void     mmu_flush_tlb(void);
void     mmu_flush_tlb_page(uint64_t vaddr);
void     mmu_flush_tlb_asid(uint16_t asid);
uint64_t mmu_get_satp(void);

#endif /* ARCH_RISCV64_MM_MMU_H */
