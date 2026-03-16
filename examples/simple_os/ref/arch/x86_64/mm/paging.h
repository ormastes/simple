/*
 * paging.h — 4-level x86_64 paging (PML4 -> PDPT -> PD -> PT)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Each level has 512 entries of 8 bytes (uint64_t).
 * Supports 4 KB pages and 2 MB huge pages.
 */

#ifndef ARCH_X86_64_MM_PAGING_H
#define ARCH_X86_64_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Page flags (PML4E / PDPTE / PDE / PTE bits) ──────────────────── */

#define PAGE_PRESENT        ((uint64_t)1 << 0)
#define PAGE_WRITABLE       ((uint64_t)1 << 1)
#define PAGE_USER           ((uint64_t)1 << 2)
#define PAGE_WRITE_THROUGH  ((uint64_t)1 << 3)
#define PAGE_CACHE_DISABLE  ((uint64_t)1 << 4)
#define PAGE_ACCESSED       ((uint64_t)1 << 5)
#define PAGE_DIRTY          ((uint64_t)1 << 6)
#define PAGE_HUGE_2MB       ((uint64_t)1 << 7)   /* PS bit in PD entry */
#define PAGE_GLOBAL         ((uint64_t)1 << 8)
#define PAGE_NX             ((uint64_t)1 << 63)   /* No-Execute (requires EFER.NXE) */

/* ── Constants ─────────────────────────────────────────────────────── */

#define PAGE_SIZE_4K        4096
#define PAGE_SIZE_2M        (2 * 1024 * 1024)
#define ENTRIES_PER_TABLE   512
#define PAGE_TABLE_POOL_SIZE 32

/* ── Address masks ─────────────────────────────────────────────────── */

/* Physical address mask (bits 12..51 for 4KB-aligned entries) */
#define PAGE_ADDR_MASK      0x000FFFFFFFFFF000ULL
#define PAGE_FLAGS_MASK     0xFFF0000000000FFFULL

/* ── Page table types (each 4096 bytes, 512 entries) ───────────────── */

typedef struct ALIGNED(PAGE_SIZE_4K) {
    uint64_t entries[ENTRIES_PER_TABLE];
} pml4_t;

typedef struct ALIGNED(PAGE_SIZE_4K) {
    uint64_t entries[ENTRIES_PER_TABLE];
} pdpt_t;

typedef struct ALIGNED(PAGE_SIZE_4K) {
    uint64_t entries[ENTRIES_PER_TABLE];
} pd_t;

typedef struct ALIGNED(PAGE_SIZE_4K) {
    uint64_t entries[ENTRIES_PER_TABLE];
} pt_t;

/* ── Public API ────────────────────────────────────────────────────── */

void     paging_init(void);
void     paging_map(uint64_t virt, uint64_t phys, uint64_t flags);
void     paging_map_2mb(uint64_t virt, uint64_t phys, uint64_t flags);
void     paging_unmap(uint64_t virt);
uint64_t paging_translate(uint64_t virt);
void     paging_identity_map_range(uint64_t start, uint64_t end,
                                   uint64_t flags);

/* Access the current kernel PML4 */
pml4_t  *paging_get_kernel_pml4(void);

#endif /* ARCH_X86_64_MM_PAGING_H */
