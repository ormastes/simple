/*
 * paging.h — Sv39 3-level page tables for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Sv39 virtual address layout (39 bits):
 *   VPN[2]:9  (bits 38:30) — Level 2 (root) index, 512 entries
 *   VPN[1]:9  (bits 29:21) — Level 1 index, 512 entries
 *   VPN[0]:9  (bits 20:12) — Level 0 index, 512 entries
 *   Offset:12 (bits 11:0)  — Page offset
 *
 * PTE format (64 bits):
 *   PPN[2]:26 | PPN[1]:9 | PPN[0]:9 | RSW:2 | D:1 | A:1 | G:1 | U:1 | X:1 | W:1 | R:1 | V:1
 *
 * Leaf types:
 *   4 KB page  — leaf at level 0
 *   2 MB megapage — leaf at level 1
 *   1 GB gigapage — leaf at level 2
 */

#ifndef ARCH_RISCV64_MM_PAGING_H
#define ARCH_RISCV64_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PTE flag bits ────────────────────────────────────────────────── */

#define PTE_V       (1UL << 0)  /* Valid                              */
#define PTE_R       (1UL << 1)  /* Readable                           */
#define PTE_W       (1UL << 2)  /* Writable                           */
#define PTE_X       (1UL << 3)  /* Executable                         */
#define PTE_U       (1UL << 4)  /* User-accessible                    */
#define PTE_G       (1UL << 5)  /* Global                             */
#define PTE_A       (1UL << 6)  /* Accessed                           */
#define PTE_D       (1UL << 7)  /* Dirty                              */

/* ── Constants ────────────────────────────────────────────────────── */

#define PAGE_SIZE           4096UL
#define MEGA_PAGE_SIZE      (2UL * 1024 * 1024)     /* 2 MB */
#define GIGA_PAGE_SIZE      (1UL * 1024 * 1024 * 1024) /* 1 GB */
#define ENTRIES_PER_TABLE   512
#define PTE_PPN_SHIFT       10
#define PAGE_TABLE_POOL_SIZE 32

/* ── Page table type ──────────────────────────────────────────────── */

typedef struct ALIGNED(PAGE_SIZE) {
    uint64_t entries[ENTRIES_PER_TABLE];
} page_table_t;

/* ── Public API ───────────────────────────────────────────────────── */

void     paging_init(void);
bool     paging_map(uint64_t virt, uint64_t phys, uint64_t flags);
void     paging_unmap(uint64_t virt);
uint64_t paging_translate(uint64_t virt);
void     paging_identity_map_range(uint64_t start, uint64_t end,
                                   uint64_t flags);

/* Access the root page table */
page_table_t *paging_get_root_table(void);

#endif /* ARCH_RISCV64_MM_PAGING_H */
