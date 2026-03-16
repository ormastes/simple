/*
 * mmu.h — MMU control register helpers for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * All functions use inline assembly to access CR0/CR2/CR3/CR4.
 */

#ifndef ARCH_X86_MM_MMU_H
#define ARCH_X86_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── CR0 bits ──────────────────────────────────────────────────────── */

#define CR0_PG  (1 << 31)   /* Paging enable                        */
#define CR0_WP  (1 << 16)   /* Write Protect (honour U/S in ring 0) */

/* ── CR4 bits ──────────────────────────────────────────────────────── */

#define CR4_PSE (1 << 4)    /* Page Size Extension (4 MB pages)     */
#define CR4_PGE (1 << 7)    /* Page Global Enable                   */

/* ── Public API ────────────────────────────────────────────────────── */

void     mmu_load_page_directory(uint32_t phys);
uint32_t mmu_get_page_directory(void);
void     mmu_enable_paging(void);
void     mmu_disable_paging(void);
void     mmu_flush_tlb(void);
void     mmu_invlpg(uint32_t addr);
void     mmu_enable_write_protect(void);
void     mmu_enable_pse(void);
void     mmu_enable_pge(void);
uint32_t mmu_get_fault_address(void);

#endif /* ARCH_X86_MM_MMU_H */
