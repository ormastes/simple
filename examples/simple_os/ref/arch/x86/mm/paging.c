/*
 * paging.c — 2-level x86 paging (4 KB pages)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86/mm/paging.h"
#include "arch/x86/mm/mmu.h"

/* ── Static storage ────────────────────────────────────────────────── */

static page_directory_t kernel_page_directory ALIGNED(PAGE_SIZE);
static page_table_t     page_table_pool[PAGE_TABLE_POOL_SIZE] ALIGNED(PAGE_SIZE);
static uint32_t         page_table_pool_next = 0;

/* ── Helpers ───────────────────────────────────────────────────────── */

static inline uint32_t pd_index(uint32_t virt)
{
    return (virt >> 22) & 0x3FF;
}

static inline uint32_t pt_index(uint32_t virt)
{
    return (virt >> 12) & 0x3FF;
}

static page_table_t *alloc_page_table(void)
{
    if (page_table_pool_next >= PAGE_TABLE_POOL_SIZE)
        return (page_table_t *)0;   /* Out of tables */

    page_table_t *pt = &page_table_pool[page_table_pool_next++];

    /* Zero out the table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        pt->entries[i] = 0;

    return pt;
}

/* ── Initialisation ────────────────────────────────────────────────── */

void paging_init(void)
{
    /* Zero the kernel page directory */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        kernel_page_directory.entries[i] = 0;

    /* Identity-map the first 4 MB (1024 pages) */
    paging_identity_map_range(0x00000000, 0x00400000,
                              PAGE_PRESENT | PAGE_WRITABLE);

    /* Load the page directory and enable paging */
    mmu_load_page_directory((uint32_t)&kernel_page_directory);
    mmu_enable_write_protect();
    mmu_enable_paging();
}

/* ── Map a single 4 KB page ────────────────────────────────────────── */

void paging_map(uint32_t virt, uint32_t phys, uint32_t flags)
{
    uint32_t pdi = pd_index(virt);
    uint32_t pti = pt_index(virt);

    page_table_t *pt;

    if (kernel_page_directory.entries[pdi] & PAGE_PRESENT) {
        /* Page table already exists */
        pt = (page_table_t *)(kernel_page_directory.entries[pdi] & 0xFFFFF000);
    } else {
        /* Allocate a new page table */
        pt = alloc_page_table();
        if (!pt)
            return;  /* Pool exhausted */

        kernel_page_directory.entries[pdi] =
            ((uint32_t)pt) | PAGE_PRESENT | PAGE_WRITABLE | (flags & PAGE_USER);
    }

    pt->entries[pti] = (phys & 0xFFFFF000) | (flags & 0xFFF) | PAGE_PRESENT;

    /* Flush the TLB entry for this virtual address */
    mmu_invlpg(virt);
}

/* ── Unmap a single 4 KB page ──────────────────────────────────────── */

void paging_unmap(uint32_t virt)
{
    uint32_t pdi = pd_index(virt);
    uint32_t pti = pt_index(virt);

    if (!(kernel_page_directory.entries[pdi] & PAGE_PRESENT))
        return;

    page_table_t *pt =
        (page_table_t *)(kernel_page_directory.entries[pdi] & 0xFFFFF000);

    pt->entries[pti] = 0;
    mmu_invlpg(virt);
}

/* ── Walk page tables to translate virtual -> physical ─────────────── */

uint32_t paging_translate(uint32_t virt)
{
    uint32_t pdi = pd_index(virt);
    uint32_t pti = pt_index(virt);

    if (!(kernel_page_directory.entries[pdi] & PAGE_PRESENT))
        return 0;  /* Not mapped */

    page_table_t *pt =
        (page_table_t *)(kernel_page_directory.entries[pdi] & 0xFFFFF000);

    if (!(pt->entries[pti] & PAGE_PRESENT))
        return 0;  /* Not mapped */

    return (pt->entries[pti] & 0xFFFFF000) | (virt & 0xFFF);
}

/* ── Identity-map a range of pages ─────────────────────────────────── */

void paging_identity_map_range(uint32_t start, uint32_t end, uint32_t flags)
{
    /* Align start down and end up to page boundaries */
    start &= ~(PAGE_SIZE - 1);

    for (uint32_t addr = start; addr < end; addr += PAGE_SIZE) {
        paging_map(addr, addr, flags);
    }
}

/* ── Accessor ──────────────────────────────────────────────────────── */

page_directory_t *paging_get_kernel_directory(void)
{
    return &kernel_page_directory;
}
