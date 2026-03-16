/*
 * paging.h — Sv32 2-level page tables for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Sv32 virtual address layout:
 *   [31:22] VPN[1]  — 10 bits, index into root page table
 *   [21:12] VPN[0]  — 10 bits, index into leaf page table
 *   [11:0]  Offset  — 12 bits, page offset
 *
 * Page Table Entry (PTE) — 32 bits:
 *   [31:20] PPN[1]  — 12 bits
 *   [19:10] PPN[0]  — 10 bits
 *   [9:8]   RSW     — 2 bits (reserved for software)
 *   [7]     D       — Dirty
 *   [6]     A       — Accessed
 *   [5]     G       — Global
 *   [4]     U       — User
 *   [3]     X       — Execute
 *   [2]     W       — Write
 *   [1]     R       — Read
 *   [0]     V       — Valid
 */

#ifndef ARCH_RISCV32_MM_PAGING_H
#define ARCH_RISCV32_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PTE flag bits ───────────────────────────────────────────────────── */

#define PTE_V       (1 << 0)    /* Valid                                */
#define PTE_R       (1 << 1)    /* Read                                 */
#define PTE_W       (1 << 2)    /* Write                                */
#define PTE_X       (1 << 3)    /* Execute                              */
#define PTE_U       (1 << 4)    /* User-accessible                      */
#define PTE_G       (1 << 5)    /* Global                               */
#define PTE_A       (1 << 6)    /* Accessed                             */
#define PTE_D       (1 << 7)    /* Dirty                                */

/* Common flag combinations */
#define PTE_RW      (PTE_R | PTE_W)
#define PTE_RX      (PTE_R | PTE_X)
#define PTE_RWX     (PTE_R | PTE_W | PTE_X)
#define PTE_KERN_RW (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D)
#define PTE_KERN_RX (PTE_V | PTE_R | PTE_X | PTE_A | PTE_D)
#define PTE_USER_RW (PTE_V | PTE_R | PTE_W | PTE_U | PTE_A | PTE_D)
#define PTE_USER_RX (PTE_V | PTE_R | PTE_X | PTE_U | PTE_A | PTE_D)

/* ── Constants ───────────────────────────────────────────────────────── */

#define PAGE_SIZE           4096
#define ENTRIES_PER_TABLE   1024
#define PAGE_TABLE_POOL_SIZE 16

/* ── Page table types ────────────────────────────────────────────────── */

typedef struct ALIGNED(PAGE_SIZE) {
    uint32_t entries[ENTRIES_PER_TABLE];
} page_table_t;

/* ── Public API ──────────────────────────────────────────────────────── */

void     paging_init(void);
void     paging_map(uint32_t virt, uint32_t phys, uint32_t flags);
void     paging_unmap(uint32_t virt);
uint32_t paging_translate(uint32_t virt);
void     paging_identity_map_range(uint32_t start, uint32_t end,
                                   uint32_t flags);

/* Access the kernel root page table */
page_table_t *paging_get_root_table(void);

#endif /* ARCH_RISCV32_MM_PAGING_H */
