/*
 * paging.h — 4-level AArch64 page tables (4 KB granule)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * 4-level page table layout (39-bit VA, T0SZ=25):
 *   L0 (PGD): bits [38:30] — 512 entries, each covers 1 GB
 *   L1 (PUD): bits [29:21] — 512 entries, each covers 2 MB
 *   L2 (PMD): bits [20:12] — 512 entries, each covers 4 KB (page)
 *
 * With T0SZ=25 (39-bit VA), we only use 3 levels (L0-L2 for page,
 * or L0 with 1GB block, L1 with 2MB block).
 *
 * For a full 4-level walk (48-bit VA, T0SZ=16):
 *   L0: bits [47:39] — 512 entries, each covers 512 GB
 *   L1: bits [38:30] — 512 entries, each covers 1 GB
 *   L2: bits [29:21] — 512 entries, each covers 2 MB
 *   L3: bits [20:12] — 512 entries, each covers 4 KB
 *
 * We use the 39-bit VA configuration (3 effective levels).
 */

#ifndef ARCH_AARCH64_MM_PAGING_H
#define ARCH_AARCH64_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Page / block descriptor bits ──────────────────────────────────── */

#define PTE_VALID           (1UL << 0)      /* Valid entry              */
#define PTE_TABLE           (1UL << 1)      /* Table descriptor (L0-L2) */
#define PTE_PAGE            (1UL << 1)      /* Page descriptor (L3)     */
#define PTE_BLOCK           (0UL << 1)      /* Block descriptor (L1/L2) */

/* Lower attributes */
#define PTE_ATTR_IDX(n)     (((uint64_t)(n) & 0x7) << 2)  /* AttrIndx[2:0] */
#define PTE_NS              (1UL << 5)      /* Non-secure              */
#define PTE_AP_RW_EL1       (0UL << 6)      /* EL1 R/W, EL0 no access */
#define PTE_AP_RW_ALL       (1UL << 6)      /* EL1 R/W, EL0 R/W       */
#define PTE_AP_RO_EL1       (2UL << 6)      /* EL1 R/O, EL0 no access */
#define PTE_AP_RO_ALL       (3UL << 6)      /* EL1 R/O, EL0 R/O       */
#define PTE_SH_NON          (0UL << 8)      /* Non-shareable           */
#define PTE_SH_OUTER        (2UL << 8)      /* Outer shareable         */
#define PTE_SH_INNER        (3UL << 8)      /* Inner shareable         */
#define PTE_AF              (1UL << 10)     /* Access Flag             */
#define PTE_NG              (1UL << 11)     /* Not global              */

/* Upper attributes */
#define PTE_PXN             (1UL << 53)     /* Privileged XN           */
#define PTE_UXN             (1UL << 54)     /* Unprivileged XN         */

/* Address mask (bits [47:12] for 4KB granule) */
#define PTE_ADDR_MASK       0x0000FFFFFFFFF000UL

/* ── Convenience combinations ──────────────────────────────────────── */

/* Kernel code/data (normal memory, WB-WA, inner shareable) */
#define PTE_KERNEL_RWX  (PTE_AF | PTE_SH_INNER | PTE_AP_RW_EL1 | \
                         PTE_ATTR_IDX(2))

/* Kernel read-only / execute */
#define PTE_KERNEL_ROX  (PTE_AF | PTE_SH_INNER | PTE_AP_RO_EL1 | \
                         PTE_ATTR_IDX(2))

/* Device memory (MMIO) */
#define PTE_DEVICE      (PTE_AF | PTE_SH_NON | PTE_AP_RW_EL1 | \
                         PTE_ATTR_IDX(0) | PTE_PXN | PTE_UXN)

/* User read/write/execute */
#define PTE_USER_RWX    (PTE_AF | PTE_SH_INNER | PTE_AP_RW_ALL | \
                         PTE_ATTR_IDX(2) | PTE_NG)

/* ── Constants ─────────────────────────────────────────────────────── */

#define PAGE_SIZE           4096
#define ENTRIES_PER_TABLE   512
#define PAGE_TABLE_POOL_SIZE 32

/* ── Page table type (512 entries of uint64_t, 4KB total) ──────────── */

typedef struct ALIGNED(PAGE_SIZE) {
    uint64_t entries[ENTRIES_PER_TABLE];
} page_table_t;

/* ── Public API ────────────────────────────────────────────────────── */

void     paging_init(void);
void     paging_map(uint64_t virt, uint64_t phys, uint64_t flags);
void     paging_unmap(uint64_t virt);
uint64_t paging_translate(uint64_t virt);
void     paging_identity_map_range(uint64_t start, uint64_t end,
                                    uint64_t flags);

page_table_t *paging_get_kernel_l0(void);

#endif /* ARCH_AARCH64_MM_PAGING_H */
