/*
 * paging.h — ARMv7 2-level page tables for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * ARMv7 Short-descriptor format (2-level):
 *   L1 table: 4096 entries * 4 bytes = 16 KB (each entry covers 1 MB)
 *   L2 table: 256 entries * 4 bytes = 1 KB (each entry covers 4 KB)
 *
 * L1 descriptor types (bits [1:0]):
 *   00 = Fault (unmapped)
 *   01 = Page table (pointer to L2 table)
 *   10 = Section (1 MB mapping) or Supersection (bit 18)
 *   11 = Reserved
 *
 * L2 descriptor types (bits [1:0]):
 *   00 = Fault
 *   01 = Large page (64 KB)
 *   1x = Small page (4 KB), bit 0 = XN
 */

#ifndef ARCH_ARM32_MM_PAGING_H
#define ARCH_ARM32_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── L1 descriptor bits ───────────────────────────────────────────── */

#define L1_FAULT            0x00
#define L1_PAGE_TABLE       0x01    /* Points to L2 table            */
#define L1_SECTION          0x02    /* 1 MB section mapping          */

/* Section bits */
#define L1_SEC_B            (1 << 2)     /* Bufferable               */
#define L1_SEC_C            (1 << 3)     /* Cacheable                */
#define L1_SEC_XN           (1 << 4)     /* Execute Never            */
#define L1_SEC_DOMAIN(d)    (((d) & 0xF) << 5)  /* Domain           */
#define L1_SEC_AP0          (1 << 10)    /* Access Permission bit 0  */
#define L1_SEC_AP1          (1 << 11)    /* Access Permission bit 1  */
#define L1_SEC_TEX(t)       (((t) & 0x7) << 12) /* Type Extension   */
#define L1_SEC_AP2          (1 << 15)    /* Access Permission bit 2  */
#define L1_SEC_S            (1 << 16)    /* Shareable                */
#define L1_SEC_nG           (1 << 17)    /* Not Global               */
#define L1_SEC_SUPER        (1 << 18)    /* Supersection             */
#define L1_SEC_NS           (1 << 19)    /* Non-Secure               */

/* Common section permission combinations */
#define L1_SEC_KERN_RW      (L1_SECTION | L1_SEC_AP0 | L1_SEC_C | L1_SEC_B)
#define L1_SEC_KERN_RO      (L1_SECTION | L1_SEC_AP0 | L1_SEC_AP2 | L1_SEC_C | L1_SEC_B)
#define L1_SEC_USER_RW      (L1_SECTION | L1_SEC_AP0 | L1_SEC_AP1 | L1_SEC_C | L1_SEC_B)
#define L1_SEC_DEVICE       (L1_SECTION | L1_SEC_AP0 | L1_SEC_B)

/* ── L2 descriptor bits (small page) ──────────────────────────────── */

#define L2_FAULT            0x00
#define L2_SMALL_PAGE       0x02    /* Small page (4 KB)             */

#define L2_SP_B             (1 << 2)     /* Bufferable               */
#define L2_SP_C             (1 << 3)     /* Cacheable                */
#define L2_SP_AP0           (1 << 4)     /* Access Permission bit 0  */
#define L2_SP_AP1           (1 << 5)     /* Access Permission bit 1  */
#define L2_SP_TEX(t)        (((t) & 0x7) << 6)  /* Type Extension   */
#define L2_SP_AP2           (1 << 9)     /* Access Permission bit 2  */
#define L2_SP_S             (1 << 10)    /* Shareable                */
#define L2_SP_nG            (1 << 11)    /* Not Global               */
#define L2_SP_XN            (1 << 0)     /* Execute Never            */

/* Common small page permission combinations */
#define L2_SP_KERN_RW       (L2_SMALL_PAGE | L2_SP_AP0 | L2_SP_C | L2_SP_B)
#define L2_SP_KERN_RO       (L2_SMALL_PAGE | L2_SP_AP0 | L2_SP_AP2 | L2_SP_C | L2_SP_B)
#define L2_SP_USER_RW       (L2_SMALL_PAGE | L2_SP_AP0 | L2_SP_AP1 | L2_SP_C | L2_SP_B)
#define L2_SP_USER_RO       (L2_SMALL_PAGE | L2_SP_AP0 | L2_SP_AP1 | L2_SP_AP2 | L2_SP_C | L2_SP_B)

/* ── Constants ─────────────────────────────────────────────────────── */

#define L1_ENTRIES          4096
#define L2_ENTRIES          256
#define SECTION_SIZE        (1 << 20)   /* 1 MB  */
#define SMALL_PAGE_SIZE     4096        /* 4 KB  */
#define L1_TABLE_SIZE       (L1_ENTRIES * 4)    /* 16 KB */
#define L2_TABLE_SIZE       (L2_ENTRIES * 4)    /* 1 KB  */
#define L2_TABLE_POOL_SIZE  32

/* ── Page table types ──────────────────────────────────────────────── */

typedef struct ALIGNED(16384) {
    uint32_t entries[L1_ENTRIES];
} l1_table_t;

typedef struct ALIGNED(1024) {
    uint32_t entries[L2_ENTRIES];
} l2_table_t;

/* ── Public API ────────────────────────────────────────────────────── */

void     paging_init(void);
void     paging_map(uint32_t virt, uint32_t phys, uint32_t flags);
void     paging_unmap(uint32_t virt);
void     paging_map_section(uint32_t virt, uint32_t phys, uint32_t flags);
void     paging_identity_map_range(uint32_t start, uint32_t end,
                                   uint32_t flags);
uint32_t paging_translate(uint32_t virt);

l1_table_t *paging_get_kernel_l1(void);

#endif /* ARCH_ARM32_MM_PAGING_H */
