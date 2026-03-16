/*
 * mmu.h — 64-bit MMU control register helpers for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Extended for long mode: CR3 holds PML4 base, CR4 has PAE,
 * EFER has LME/NXE/SCE.
 */

#ifndef ARCH_X86_64_MM_MMU_H
#define ARCH_X86_64_MM_MMU_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── CR0 bits ──────────────────────────────────────────────────────── */

#define CR0_PG  ((uint64_t)1 << 31)   /* Paging enable                */
#define CR0_WP  ((uint64_t)1 << 16)   /* Write Protect                */

/* ── CR4 bits ──────────────────────────────────────────────────────── */

#define CR4_PAE (1 << 5)    /* Physical Address Extension (required)   */
#define CR4_PGE (1 << 7)    /* Page Global Enable                      */
#define CR4_PSE (1 << 4)    /* Page Size Extension                     */

/* ── EFER MSR bits ─────────────────────────────────────────────────── */

#define MSR_EFER    0xC0000080
#define EFER_SCE    (1 << 0)    /* System Call Extensions (SYSCALL)    */
#define EFER_LME    (1 << 8)    /* Long Mode Enable                   */
#define EFER_NXE    (1 << 11)   /* No-Execute Enable                  */

/* ── Public API ────────────────────────────────────────────────────── */

/* CR3: PML4 base */
void     mmu_load_pml4(uint64_t phys);
uint64_t mmu_get_pml4(void);

/* TLB management */
void     mmu_flush_tlb(void);
void     mmu_invlpg(uint64_t addr);

/* CR0 helpers */
void     mmu_enable_write_protect(void);

/* CR4 helpers */
void     mmu_enable_pge(void);

/* EFER helpers */
void     mmu_enable_nx(void);
void     mmu_enable_syscall(void);

/* CR2: fault address */
uint64_t mmu_get_fault_address(void);

/* MSR read/write */
uint64_t mmu_read_msr(uint32_t msr);
void     mmu_write_msr(uint32_t msr, uint64_t val);

#endif /* ARCH_X86_64_MM_MMU_H */
