/*
 * paging.c — 4-level AArch64 page tables (4 KB granule)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * For the initial kernel setup with T0SZ=25 (39-bit VA, 512 GB),
 * we use 3 levels: L0 -> L1 -> L2 (page entries).
 * L0[i] covers 1 GB, L1[i] covers 2 MB, L2[i] covers 4 KB.
 *
 * For simplicity, the initial mapping identity-maps the first 1 GB
 * using a single L0 entry pointing to an L1 table with 2 MB block
 * entries. This avoids needing L2 tables for the initial boot.
 */

#include "arch/aarch64/mm/paging.h"
#include "arch/aarch64/mm/mmu.h"

/* ── Static storage ────────────────────────────────────────────────── */

static page_table_t kernel_l0 ALIGNED(PAGE_SIZE);   /* L0 (PGD)        */
static page_table_t page_table_pool[PAGE_TABLE_POOL_SIZE] ALIGNED(PAGE_SIZE);
static uint32_t     page_table_pool_next = 0;

/* ── Helpers ───────────────────────────────────────────────────────── */

/* L0 index: bits [38:30] for 39-bit VA */
static inline uint32_t l0_index(uint64_t virt)
{
    return (uint32_t)((virt >> 30) & 0x1FF);
}

/* L1 index: bits [29:21] */
static inline uint32_t l1_index(uint64_t virt)
{
    return (uint32_t)((virt >> 21) & 0x1FF);
}

/* L2 index: bits [20:12] */
static inline uint32_t l2_index(uint64_t virt)
{
    return (uint32_t)((virt >> 12) & 0x1FF);
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
    /* Zero the L0 table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        kernel_l0.entries[i] = 0;

    /*
     * Identity-map the first 1 GB using 2 MB block entries at L1.
     * This covers QEMU virt's RAM (starting at 0x40000000) and
     * device MMIO regions (0x00000000 - 0x3FFFFFFF).
     */

    /* Allocate L1 table for the first 1 GB (L0 index 0) */
    page_table_t *l1_table = alloc_page_table();
    if (!l1_table)
        return;

    /* Fill L1 with 2 MB block entries for 0x00000000 - 0x3FFFFFFF (device) */
    for (uint32_t i = 0; i < 512; i++) {
        uint64_t phys = (uint64_t)i * (2 * 1024 * 1024);
        l1_table->entries[i] = phys | PTE_VALID | PTE_BLOCK |
                               PTE_DEVICE;
    }

    /* L0[0] = table entry pointing to L1 */
    kernel_l0.entries[0] = ((uint64_t)l1_table) | PTE_VALID | PTE_TABLE;

    /* Allocate L1 table for second 1 GB (L0 index 1): RAM at 0x40000000 */
    page_table_t *l1_ram = alloc_page_table();
    if (!l1_ram)
        return;

    for (uint32_t i = 0; i < 512; i++) {
        uint64_t phys = 0x40000000UL + (uint64_t)i * (2 * 1024 * 1024);
        l1_ram->entries[i] = phys | PTE_VALID | PTE_BLOCK |
                             PTE_KERNEL_RWX;
    }

    kernel_l0.entries[1] = ((uint64_t)l1_ram) | PTE_VALID | PTE_TABLE;

    /* Configure MMU and load page tables */
    mmu_init();
    mmu_set_ttbr0((uint64_t)&kernel_l0);
    mmu_flush_tlb();
    mmu_enable();
}

/* ── Map a single 4 KB page (full 3-level walk) ───────────────────── */

void paging_map(uint64_t virt, uint64_t phys, uint64_t flags)
{
    uint32_t l0i = l0_index(virt);
    uint32_t l1i = l1_index(virt);
    uint32_t l2i = l2_index(virt);

    /* Ensure L1 table exists */
    page_table_t *l1;
    if (kernel_l0.entries[l0i] & PTE_VALID) {
        l1 = (page_table_t *)(kernel_l0.entries[l0i] & PTE_ADDR_MASK);
    } else {
        l1 = alloc_page_table();
        if (!l1) return;
        kernel_l0.entries[l0i] = ((uint64_t)l1) | PTE_VALID | PTE_TABLE;
    }

    /* Ensure L2 table exists */
    page_table_t *l2;
    if (l1->entries[l1i] & PTE_VALID) {
        /* Check if it's a block entry — can't split for now */
        if (!(l1->entries[l1i] & PTE_TABLE)) {
            return;  /* Can't split 2MB block into 4KB pages */
        }
        l2 = (page_table_t *)(l1->entries[l1i] & PTE_ADDR_MASK);
    } else {
        l2 = alloc_page_table();
        if (!l2) return;
        l1->entries[l1i] = ((uint64_t)l2) | PTE_VALID | PTE_TABLE;
    }

    /* L2 page entry (L3 equivalent in 4-level, but we use 3-level) */
    l2->entries[l2i] = (phys & PTE_ADDR_MASK) | flags | PTE_VALID | PTE_PAGE;

    mmu_invalidate_addr(virt);
}

/* ── Unmap a single 4 KB page ──────────────────────────────────────── */

void paging_unmap(uint64_t virt)
{
    uint32_t l0i = l0_index(virt);
    uint32_t l1i = l1_index(virt);
    uint32_t l2i = l2_index(virt);

    if (!(kernel_l0.entries[l0i] & PTE_VALID))
        return;

    page_table_t *l1 = (page_table_t *)(kernel_l0.entries[l0i] & PTE_ADDR_MASK);

    if (!(l1->entries[l1i] & PTE_VALID) || !(l1->entries[l1i] & PTE_TABLE))
        return;

    page_table_t *l2 = (page_table_t *)(l1->entries[l1i] & PTE_ADDR_MASK);

    l2->entries[l2i] = 0;
    mmu_invalidate_addr(virt);
}

/* ── Walk page tables to translate virtual -> physical ─────────────── */

uint64_t paging_translate(uint64_t virt)
{
    uint32_t l0i = l0_index(virt);

    if (!(kernel_l0.entries[l0i] & PTE_VALID))
        return 0;

    page_table_t *l1 = (page_table_t *)(kernel_l0.entries[l0i] & PTE_ADDR_MASK);
    uint32_t l1i = l1_index(virt);

    if (!(l1->entries[l1i] & PTE_VALID))
        return 0;

    /* Check for 2 MB block entry */
    if (!(l1->entries[l1i] & PTE_TABLE)) {
        uint64_t block_phys = l1->entries[l1i] & 0x0000FFFFFFE00000UL;
        return block_phys | (virt & 0x1FFFFF);
    }

    page_table_t *l2 = (page_table_t *)(l1->entries[l1i] & PTE_ADDR_MASK);
    uint32_t l2i = l2_index(virt);

    if (!(l2->entries[l2i] & PTE_VALID))
        return 0;

    return (l2->entries[l2i] & PTE_ADDR_MASK) | (virt & 0xFFF);
}

/* ── Identity-map a range of pages ─────────────────────────────────── */

void paging_identity_map_range(uint64_t start, uint64_t end, uint64_t flags)
{
    start &= ~(uint64_t)(PAGE_SIZE - 1);

    for (uint64_t addr = start; addr < end; addr += PAGE_SIZE) {
        paging_map(addr, addr, flags);
    }
}

/* ── Accessor ──────────────────────────────────────────────────────── */

page_table_t *paging_get_kernel_l0(void)
{
    return &kernel_l0;
}
