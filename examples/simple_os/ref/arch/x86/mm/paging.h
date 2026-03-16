/*
 * paging.h — 2-level x86 paging (4 KB pages)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_MM_PAGING_H
#define ARCH_X86_MM_PAGING_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Page flags (PDE / PTE bits) ───────────────────────────────────── */

#define PAGE_PRESENT        (1 << 0)
#define PAGE_WRITABLE       (1 << 1)
#define PAGE_USER           (1 << 2)
#define PAGE_WRITE_THROUGH  (1 << 3)
#define PAGE_CACHE_DISABLE  (1 << 4)
#define PAGE_ACCESSED       (1 << 5)
#define PAGE_DIRTY          (1 << 6)
#define PAGE_SIZE_4MB       (1 << 7)    /* Only in PDE */

/* ── Constants ─────────────────────────────────────────────────────── */

#define PAGE_SIZE           4096
#define ENTRIES_PER_TABLE   1024
#define PAGE_TABLE_POOL_SIZE 16

/* ── Page directory / page table types ─────────────────────────────── */

typedef struct ALIGNED(PAGE_SIZE) {
    uint32_t entries[ENTRIES_PER_TABLE];
} page_directory_t;

typedef struct ALIGNED(PAGE_SIZE) {
    uint32_t entries[ENTRIES_PER_TABLE];
} page_table_t;

/* ── Public API ────────────────────────────────────────────────────── */

void     paging_init(void);
void     paging_map(uint32_t virt, uint32_t phys, uint32_t flags);
void     paging_unmap(uint32_t virt);
uint32_t paging_translate(uint32_t virt);
void     paging_identity_map_range(uint32_t start, uint32_t end,
                                   uint32_t flags);

/* Access the current kernel page directory */
page_directory_t *paging_get_kernel_directory(void);

#endif /* ARCH_X86_MM_PAGING_H */
