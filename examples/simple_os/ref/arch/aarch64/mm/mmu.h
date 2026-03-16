/*
 * mmu.h — AArch64 MMU control (SCTLR_EL1, TCR_EL1, MAIR_EL1, TTBR)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_AARCH64_MM_MMU_H
#define ARCH_AARCH64_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── SCTLR_EL1 bits ───────────────────────────────────────────────── */

#define SCTLR_M     (1 << 0)    /* MMU enable                        */
#define SCTLR_A     (1 << 1)    /* Alignment check enable             */
#define SCTLR_C     (1 << 2)    /* Data cache enable                  */
#define SCTLR_I     (1 << 12)   /* Instruction cache enable           */
#define SCTLR_WXN   (1 << 19)   /* Write implies XN                   */

/* ── TCR_EL1 bits ──────────────────────────────────────────────────── */

#define TCR_T0SZ(n)     ((n) & 0x3F)        /* TTBR0 region size      */
#define TCR_T1SZ(n)     (((n) & 0x3F) << 16)/* TTBR1 region size      */
#define TCR_TG0_4KB     (0UL << 14)         /* TTBR0 granule 4KB      */
#define TCR_TG1_4KB     (2UL << 30)         /* TTBR1 granule 4KB      */
#define TCR_SH0_INNER   (3UL << 12)         /* Inner shareable        */
#define TCR_SH1_INNER   (3UL << 28)         /* Inner shareable        */
#define TCR_ORGN0_WBWA  (1UL << 10)         /* Outer WB-WA cacheable  */
#define TCR_IRGN0_WBWA  (1UL << 8)          /* Inner WB-WA cacheable  */
#define TCR_ORGN1_WBWA  (1UL << 26)         /* Outer WB-WA cacheable  */
#define TCR_IRGN1_WBWA  (1UL << 24)         /* Inner WB-WA cacheable  */
#define TCR_IPS_40BIT   (2UL << 32)         /* 40-bit PA (1TB)        */

/* ── MAIR_EL1 attribute indices ────────────────────────────────────── */

#define MAIR_DEVICE_nGnRnE  0x00    /* Device-nGnRnE (strongly ordered) */
#define MAIR_NORMAL_NC      0x44    /* Normal non-cacheable              */
#define MAIR_NORMAL_WB_WA   0xFF    /* Normal WB-WA (inner + outer)      */

#define MAIR_IDX_DEVICE     0       /* Index 0: Device memory            */
#define MAIR_IDX_NORMAL_NC  1       /* Index 1: Normal non-cacheable     */
#define MAIR_IDX_NORMAL     2       /* Index 2: Normal WB-WA cacheable   */

/* ── Public API ────────────────────────────────────────────────────── */

void     mmu_init(void);
void     mmu_enable(void);
void     mmu_disable(void);
void     mmu_set_ttbr0(uint64_t phys);
void     mmu_set_ttbr1(uint64_t phys);
uint64_t mmu_get_ttbr0(void);
uint64_t mmu_get_ttbr1(void);
void     mmu_flush_tlb(void);
void     mmu_invalidate_addr(uint64_t vaddr);
void     mmu_dsb(void);
void     mmu_isb(void);

#endif /* ARCH_AARCH64_MM_MMU_H */
