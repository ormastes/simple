/*
 * paging.c — Sv39 3-level page tables for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/mm/paging.h"
#include "arch/riscv64/mm/mmu.h"

/* ── Static storage ───────────────────────────────────────────────── */

static page_table_t kernel_root_table ALIGNED(PAGE_SIZE);
static page_table_t page_table_pool[PAGE_TABLE_POOL_SIZE] ALIGNED(PAGE_SIZE);
static uint32_t     page_table_pool_next = 0;

/* ── Helpers ──────────────────────────────────────────────────────── */

static inline uint64_t vpn2(uint64_t virt)
{
    return (virt >> 30) & 0x1FF;
}

static inline uint64_t vpn1(uint64_t virt)
{
    return (virt >> 21) & 0x1FF;
}

static inline uint64_t vpn0(uint64_t virt)
{
    return (virt >> 12) & 0x1FF;
}

static inline uint64_t pte_to_phys(uint64_t pte)
{
    return ((pte >> PTE_PPN_SHIFT) << 12);
}

static inline uint64_t phys_to_pte(uint64_t phys, uint64_t flags)
{
    return ((phys >> 12) << PTE_PPN_SHIFT) | flags;
}

static inline bool pte_is_valid(uint64_t pte)
{
    return (pte & PTE_V) != 0;
}

static inline bool pte_is_leaf(uint64_t pte)
{
    return (pte & (PTE_R | PTE_W | PTE_X)) != 0;
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

/* ── Initialisation ───────────────────────────────────────────────── */

void paging_init(void)
{
    /* Zero the root page table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        kernel_root_table.entries[i] = 0;

    /* Identity-map the first 128 MB (enough for kernel + peripherals) */
    paging_identity_map_range(0x80000000UL, 0x88000000UL,
                              PTE_R | PTE_W | PTE_X);

    /* Identity-map UART MMIO region */
    paging_identity_map_range(0x10000000UL, 0x10001000UL,
                              PTE_R | PTE_W);

    /* Enable Sv39 paging */
    mmu_enable((uint64_t)&kernel_root_table, 0);
}

/* ── Map a single 4 KB page ───────────────────────────────────────── */

bool paging_map(uint64_t virt, uint64_t phys, uint64_t flags)
{
    uint64_t idx2 = vpn2(virt);
    uint64_t idx1 = vpn1(virt);
    uint64_t idx0 = vpn0(virt);

    /* Level 2 -> Level 1 */
    page_table_t *l1;
    if (pte_is_valid(kernel_root_table.entries[idx2])) {
        l1 = (page_table_t *)pte_to_phys(kernel_root_table.entries[idx2]);
    } else {
        l1 = alloc_page_table();
        if (!l1)
            return false;
        kernel_root_table.entries[idx2] = phys_to_pte((uint64_t)l1, PTE_V);
    }

    /* Level 1 -> Level 0 */
    page_table_t *l0;
    if (pte_is_valid(l1->entries[idx1])) {
        l0 = (page_table_t *)pte_to_phys(l1->entries[idx1]);
    } else {
        l0 = alloc_page_table();
        if (!l0)
            return false;
        l1->entries[idx1] = phys_to_pte((uint64_t)l0, PTE_V);
    }

    /* Level 0: leaf entry */
    l0->entries[idx0] = phys_to_pte(phys, flags | PTE_V | PTE_A | PTE_D);

    /* Flush TLB for this address */
    mmu_flush_tlb_page(virt);

    return true;
}

/* ── Unmap a single 4 KB page ─────────────────────────────────────── */

void paging_unmap(uint64_t virt)
{
    uint64_t idx2 = vpn2(virt);
    uint64_t idx1 = vpn1(virt);
    uint64_t idx0 = vpn0(virt);

    if (!pte_is_valid(kernel_root_table.entries[idx2]))
        return;

    page_table_t *l1 = (page_table_t *)pte_to_phys(kernel_root_table.entries[idx2]);

    if (!pte_is_valid(l1->entries[idx1]))
        return;

    page_table_t *l0 = (page_table_t *)pte_to_phys(l1->entries[idx1]);

    l0->entries[idx0] = 0;
    mmu_flush_tlb_page(virt);
}

/* ── Translate virtual to physical ────────────────────────────────── */

uint64_t paging_translate(uint64_t virt)
{
    uint64_t idx2 = vpn2(virt);
    uint64_t idx1 = vpn1(virt);
    uint64_t idx0 = vpn0(virt);

    if (!pte_is_valid(kernel_root_table.entries[idx2]))
        return 0;

    uint64_t pte2 = kernel_root_table.entries[idx2];
    if (pte_is_leaf(pte2)) {
        /* 1 GB gigapage */
        return pte_to_phys(pte2) | (virt & (GIGA_PAGE_SIZE - 1));
    }

    page_table_t *l1 = (page_table_t *)pte_to_phys(pte2);
    if (!pte_is_valid(l1->entries[idx1]))
        return 0;

    uint64_t pte1 = l1->entries[idx1];
    if (pte_is_leaf(pte1)) {
        /* 2 MB megapage */
        return pte_to_phys(pte1) | (virt & (MEGA_PAGE_SIZE - 1));
    }

    page_table_t *l0 = (page_table_t *)pte_to_phys(pte1);
    if (!pte_is_valid(l0->entries[idx0]))
        return 0;

    /* 4 KB page */
    return pte_to_phys(l0->entries[idx0]) | (virt & (PAGE_SIZE - 1));
}

/* ── Identity-map a range ─────────────────────────────────────────── */

void paging_identity_map_range(uint64_t start, uint64_t end, uint64_t flags)
{
    start &= ~(PAGE_SIZE - 1);

    for (uint64_t addr = start; addr < end; addr += PAGE_SIZE) {
        paging_map(addr, addr, flags);
    }
}

/* ── Accessor ─────────────────────────────────────────────────────── */

page_table_t *paging_get_root_table(void)
{
    return &kernel_root_table;
}
