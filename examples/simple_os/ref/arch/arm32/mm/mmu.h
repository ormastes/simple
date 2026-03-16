/*
 * mmu.h — ARMv7 MMU control for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Uses CP15 coprocessor registers for MMU configuration.
 *
 * Key CP15 registers:
 *   c1 (SCTLR)  — System Control (M bit = MMU enable)
 *   c2 (TTBR0)  — Translation Table Base Register 0
 *   c2 (TTBR1)  — Translation Table Base Register 1
 *   c2 (TTBCR)  — Translation Table Base Control
 *   c3 (DACR)   — Domain Access Control
 *   c7          — Cache maintenance
 *   c8          — TLB maintenance
 */

#ifndef ARCH_ARM32_MM_MMU_H
#define ARCH_ARM32_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── SCTLR bits (CP15 c1) ─────────────────────────────────────────── */

#define SCTLR_M        (1 << 0)     /* MMU enable                   */
#define SCTLR_A        (1 << 1)     /* Alignment fault enable       */
#define SCTLR_C        (1 << 2)     /* Data cache enable            */
#define SCTLR_W        (1 << 3)     /* Write buffer enable          */
#define SCTLR_Z        (1 << 11)    /* Branch prediction enable     */
#define SCTLR_I        (1 << 12)    /* Instruction cache enable     */
#define SCTLR_V        (1 << 13)    /* High vectors (0xFFFF0000)    */
#define SCTLR_AFE      (1 << 29)    /* Access Flag Enable           */
#define SCTLR_TRE      (1 << 28)    /* TEX remap enable             */

/* ── Domain Access Control values ──────────────────────────────────── */

#define DACR_NO_ACCESS  0x00
#define DACR_CLIENT     0x01
#define DACR_MANAGER    0x03

/* ── Public API ────────────────────────────────────────────────────── */

void     mmu_init(void);
void     mmu_enable(void);
void     mmu_disable(void);
void     mmu_set_ttbr0(uint32_t table_phys);
uint32_t mmu_get_ttbr0(void);
void     mmu_set_ttbr1(uint32_t table_phys);
void     mmu_set_ttbcr(uint32_t val);
void     mmu_set_dacr(uint32_t val);
void     mmu_flush_tlb(void);
void     mmu_invalidate_tlb_entry(uint32_t vaddr);
void     mmu_invalidate_icache(void);
void     mmu_clean_dcache(void);
void     mmu_dsb(void);
void     mmu_isb(void);

#endif /* ARCH_ARM32_MM_MMU_H */
