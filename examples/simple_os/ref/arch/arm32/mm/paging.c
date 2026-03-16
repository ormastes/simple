/*
 * paging.c — ARMv7 2-level page tables for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/mm/paging.h"
#include "arch/arm32/mm/mmu.h"

/* ── Static storage ────────────────────────────────────────────────── */

static l1_table_t kernel_l1 ALIGNED(16384);
static l2_table_t l2_pool[L2_TABLE_POOL_SIZE] ALIGNED(1024);
static uint32_t   l2_pool_next = 0;

/* ── Helpers ───────────────────────────────────────────────────────── */

static inline uint32_t l1_index(uint32_t virt)
{
    return (virt >> 20) & 0xFFF;
}

static inline uint32_t l2_index(uint32_t virt)
{
    return (virt >> 12) & 0xFF;
}

static l2_table_t *alloc_l2_table(void)
{
    if (l2_pool_next >= L2_TABLE_POOL_SIZE)
        return (l2_table_t *)0;

    l2_table_t *l2 = &l2_pool[l2_pool_next++];

    /* Zero out the table */
    for (int i = 0; i < L2_ENTRIES; i++)
        l2->entries[i] = 0;

    return l2;
}

/* ── Initialisation ────────────────────────────────────────────────── */

void paging_init(void)
{
    /* Zero the L1 table */
    for (int i = 0; i < L1_ENTRIES; i++)
        kernel_l1.entries[i] = 0;

    /*
     * Identity-map the first 256 MB as sections for early boot.
     * This covers kernel code/data and QEMU virt peripherals.
     */
    paging_identity_map_range(0x00000000, 0x10000000,
                              L1_SEC_KERN_RW);

    /* Map UART and GIC as device memory (no cache) */
    paging_map_section(0x08000000, 0x08000000, L1_SEC_DEVICE);  /* GIC */
    paging_map_section(0x09000000, 0x09000000, L1_SEC_DEVICE);  /* UART */

    /* Set up MMU */
    mmu_init();
    mmu_set_ttbr0((uint32_t)&kernel_l1);
    mmu_flush_tlb();
    mmu_enable();
}

/* ── Map a 4 KB page (uses L2 table) ──────────────────────────────── */

void paging_map(uint32_t virt, uint32_t phys, uint32_t flags)
{
    uint32_t l1i = l1_index(virt);
    uint32_t l2i = l2_index(virt);

    l2_table_t *l2;

    if ((kernel_l1.entries[l1i] & 0x3) == L1_PAGE_TABLE) {
        /* L2 table already allocated */
        l2 = (l2_table_t *)(kernel_l1.entries[l1i] & 0xFFFFFC00);
    } else {
        /* Allocate a new L2 table */
        l2 = alloc_l2_table();
        if (!l2)
            return;

        /* Write L1 entry: page table descriptor */
        kernel_l1.entries[l1i] = ((uint32_t)l2) | L1_PAGE_TABLE;
    }

    /* Write L2 entry: small page descriptor */
    l2->entries[l2i] = (phys & 0xFFFFF000) | (flags & 0xFFF) | L2_SMALL_PAGE;

    mmu_invalidate_tlb_entry(virt);
}

/* ── Map a 1 MB section (direct L1 entry) ──────────────────────────── */

void paging_map_section(uint32_t virt, uint32_t phys, uint32_t flags)
{
    uint32_t l1i = l1_index(virt);
    kernel_l1.entries[l1i] = (phys & 0xFFF00000) | flags;
    mmu_invalidate_tlb_entry(virt);
}

/* ── Unmap a 4 KB page ─────────────────────────────────────────────── */

void paging_unmap(uint32_t virt)
{
    uint32_t l1i = l1_index(virt);
    uint32_t l2i = l2_index(virt);

    if ((kernel_l1.entries[l1i] & 0x3) != L1_PAGE_TABLE)
        return;

    l2_table_t *l2 = (l2_table_t *)(kernel_l1.entries[l1i] & 0xFFFFFC00);
    l2->entries[l2i] = L2_FAULT;

    mmu_invalidate_tlb_entry(virt);
}

/* ── Translate virtual to physical ─────────────────────────────────── */

uint32_t paging_translate(uint32_t virt)
{
    uint32_t l1i = l1_index(virt);
    uint32_t l1_entry = kernel_l1.entries[l1i];

    if ((l1_entry & 0x3) == L1_SECTION) {
        /* Section mapping */
        return (l1_entry & 0xFFF00000) | (virt & 0x000FFFFF);
    }

    if ((l1_entry & 0x3) == L1_PAGE_TABLE) {
        /* Page table mapping */
        l2_table_t *l2 = (l2_table_t *)(l1_entry & 0xFFFFFC00);
        uint32_t l2i = l2_index(virt);
        uint32_t l2_entry = l2->entries[l2i];

        if ((l2_entry & 0x2) == 0)
            return 0;  /* Not mapped */

        return (l2_entry & 0xFFFFF000) | (virt & 0x00000FFF);
    }

    return 0;  /* Fault entry — not mapped */
}

/* ── Identity-map a range as sections ──────────────────────────────── */

void paging_identity_map_range(uint32_t start, uint32_t end, uint32_t flags)
{
    /* Align to section boundaries */
    start &= ~(SECTION_SIZE - 1);

    for (uint32_t addr = start; addr < end; addr += SECTION_SIZE) {
        paging_map_section(addr, addr, flags);
    }
}

/* ── Accessor ──────────────────────────────────────────────────────── */

l1_table_t *paging_get_kernel_l1(void)
{
    return &kernel_l1;
}
