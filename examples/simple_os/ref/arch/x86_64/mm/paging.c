/*
 * paging.c — 4-level x86_64 paging (PML4 -> PDPT -> PD -> PT)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/mm/paging.h"
#include "arch/x86_64/mm/mmu.h"

/* ── Static storage ────────────────────────────────────────────────── */

static pml4_t kernel_pml4 ALIGNED(PAGE_SIZE_4K);

/* Generic page table pool (used for PDPT, PD, and PT allocations) */
typedef struct ALIGNED(PAGE_SIZE_4K) {
    uint64_t entries[ENTRIES_PER_TABLE];
} page_table_generic_t;

static page_table_generic_t page_table_pool[PAGE_TABLE_POOL_SIZE] ALIGNED(PAGE_SIZE_4K);
static uint32_t             page_table_pool_next = 0;

/* ── Helpers ───────────────────────────────────────────────────────── */

/* Extract index at each paging level from a 64-bit virtual address */
static inline uint32_t pml4_index(uint64_t virt) { return (uint32_t)((virt >> 39) & 0x1FF); }
static inline uint32_t pdpt_index(uint64_t virt) { return (uint32_t)((virt >> 30) & 0x1FF); }
static inline uint32_t pd_index(uint64_t virt)   { return (uint32_t)((virt >> 21) & 0x1FF); }
static inline uint32_t pt_index(uint64_t virt)   { return (uint32_t)((virt >> 12) & 0x1FF); }

static page_table_generic_t *alloc_page_table(void)
{
    if (page_table_pool_next >= PAGE_TABLE_POOL_SIZE)
        return (page_table_generic_t *)0;   /* Out of tables */

    page_table_generic_t *tbl = &page_table_pool[page_table_pool_next++];

    /* Zero out the table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        tbl->entries[i] = 0;

    return tbl;
}

/* Ensure a child table exists at parent[index]; allocate if needed. */
static uint64_t *ensure_table(uint64_t *parent, uint32_t index, uint64_t flags)
{
    if (parent[index] & PAGE_PRESENT) {
        return (uint64_t *)(parent[index] & PAGE_ADDR_MASK);
    }

    page_table_generic_t *child = alloc_page_table();
    if (!child)
        return (uint64_t *)0;

    parent[index] = ((uint64_t)child) | PAGE_PRESENT | PAGE_WRITABLE | (flags & PAGE_USER);
    return (uint64_t *)child;
}

/* ── Initialisation ────────────────────────────────────────────────── */

void paging_init(void)
{
    /* Zero the kernel PML4 */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        kernel_pml4.entries[i] = 0;

    /* Identity-map the first 4 MB (two 2MB pages) */
    paging_map_2mb(0x00000000, 0x00000000, PAGE_PRESENT | PAGE_WRITABLE);
    paging_map_2mb(0x00200000, 0x00200000, PAGE_PRESENT | PAGE_WRITABLE);

    /* Load the PML4 */
    mmu_load_pml4((uint64_t)&kernel_pml4);
}

/* ── Map a single 4 KB page ──────────────────────────────────────── */

void paging_map(uint64_t virt, uint64_t phys, uint64_t flags)
{
    uint64_t *pdpt_tbl = ensure_table(kernel_pml4.entries, pml4_index(virt), flags);
    if (!pdpt_tbl) return;

    uint64_t *pd_tbl = ensure_table(pdpt_tbl, pdpt_index(virt), flags);
    if (!pd_tbl) return;

    uint64_t *pt_tbl = ensure_table(pd_tbl, pd_index(virt), flags);
    if (!pt_tbl) return;

    pt_tbl[pt_index(virt)] = (phys & PAGE_ADDR_MASK) | (flags & ~PAGE_ADDR_MASK) | PAGE_PRESENT;

    mmu_invlpg(virt);
}

/* ── Map a 2 MB huge page ────────────────────────────────────────── */

void paging_map_2mb(uint64_t virt, uint64_t phys, uint64_t flags)
{
    uint64_t *pdpt_tbl = ensure_table(kernel_pml4.entries, pml4_index(virt), flags);
    if (!pdpt_tbl) return;

    uint64_t *pd_tbl = ensure_table(pdpt_tbl, pdpt_index(virt), flags);
    if (!pd_tbl) return;

    /* Set PD entry with PS (huge page) bit */
    pd_tbl[pd_index(virt)] = (phys & 0xFFFFFFFFFFE00000ULL) | flags | PAGE_HUGE_2MB | PAGE_PRESENT;

    mmu_invlpg(virt);
}

/* ── Unmap a single 4 KB page ────────────────────────────────────── */

void paging_unmap(uint64_t virt)
{
    uint32_t pml4i = pml4_index(virt);
    if (!(kernel_pml4.entries[pml4i] & PAGE_PRESENT))
        return;

    uint64_t *pdpt_tbl = (uint64_t *)(kernel_pml4.entries[pml4i] & PAGE_ADDR_MASK);
    uint32_t pdpti = pdpt_index(virt);
    if (!(pdpt_tbl[pdpti] & PAGE_PRESENT))
        return;

    uint64_t *pd_tbl = (uint64_t *)(pdpt_tbl[pdpti] & PAGE_ADDR_MASK);
    uint32_t pdi = pd_index(virt);
    if (!(pd_tbl[pdi] & PAGE_PRESENT))
        return;

    /* If this is a 2MB page, just clear the PD entry */
    if (pd_tbl[pdi] & PAGE_HUGE_2MB) {
        pd_tbl[pdi] = 0;
        mmu_invlpg(virt);
        return;
    }

    uint64_t *pt_tbl = (uint64_t *)(pd_tbl[pdi] & PAGE_ADDR_MASK);
    pt_tbl[pt_index(virt)] = 0;
    mmu_invlpg(virt);
}

/* ── Walk page tables to translate virtual -> physical ─────────────── */

uint64_t paging_translate(uint64_t virt)
{
    uint32_t pml4i = pml4_index(virt);
    if (!(kernel_pml4.entries[pml4i] & PAGE_PRESENT))
        return 0;

    uint64_t *pdpt_tbl = (uint64_t *)(kernel_pml4.entries[pml4i] & PAGE_ADDR_MASK);
    uint32_t pdpti = pdpt_index(virt);
    if (!(pdpt_tbl[pdpti] & PAGE_PRESENT))
        return 0;

    uint64_t *pd_tbl = (uint64_t *)(pdpt_tbl[pdpti] & PAGE_ADDR_MASK);
    uint32_t pdi = pd_index(virt);
    if (!(pd_tbl[pdi] & PAGE_PRESENT))
        return 0;

    /* Check for 2MB huge page */
    if (pd_tbl[pdi] & PAGE_HUGE_2MB) {
        return (pd_tbl[pdi] & 0xFFFFFFFFFFE00000ULL) | (virt & 0x1FFFFF);
    }

    uint64_t *pt_tbl = (uint64_t *)(pd_tbl[pdi] & PAGE_ADDR_MASK);
    uint32_t pti = pt_index(virt);
    if (!(pt_tbl[pti] & PAGE_PRESENT))
        return 0;

    return (pt_tbl[pti] & PAGE_ADDR_MASK) | (virt & 0xFFF);
}

/* ── Identity-map a range of 4 KB pages ───────────────────────────── */

void paging_identity_map_range(uint64_t start, uint64_t end, uint64_t flags)
{
    start &= ~(PAGE_SIZE_4K - 1);

    for (uint64_t addr = start; addr < end; addr += PAGE_SIZE_4K) {
        paging_map(addr, addr, flags);
    }
}

/* ── Accessor ──────────────────────────────────────────────────────── */

pml4_t *paging_get_kernel_pml4(void)
{
    return &kernel_pml4;
}
