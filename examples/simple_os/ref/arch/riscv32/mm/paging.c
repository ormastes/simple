/*
 * paging.c — Sv32 2-level page tables for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/mm/paging.h"
#include "arch/riscv32/mm/mmu.h"

/* ── Static storage ──────────────────────────────────────────────────── */

static page_table_t kernel_root_table ALIGNED(PAGE_SIZE);
static page_table_t page_table_pool[PAGE_TABLE_POOL_SIZE] ALIGNED(PAGE_SIZE);
static uint32_t     page_table_pool_next = 0;

/* ── Helpers ─────────────────────────────────────────────────────────── */

static inline uint32_t vpn1(uint32_t virt)
{
    return (virt >> 22) & 0x3FF;
}

static inline uint32_t vpn0(uint32_t virt)
{
    return (virt >> 12) & 0x3FF;
}

static inline uint32_t pte_to_ppn(uint32_t pte)
{
    return (pte >> 10);
}

static inline uint32_t pte_to_phys(uint32_t pte)
{
    return (pte >> 10) << 12;
}

static inline uint32_t phys_to_pte(uint32_t phys, uint32_t flags)
{
    return ((phys >> 12) << 10) | flags;
}

static page_table_t *alloc_page_table(void)
{
    if (page_table_pool_next >= PAGE_TABLE_POOL_SIZE)
        return (page_table_t *)0;

    page_table_t *pt = &page_table_pool[page_table_pool_next++];

    /* Zero out the table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        pt->entries[i] = 0;

    return pt;
}

/* ── Initialisation ──────────────────────────────────────────────────── */

void paging_init(void)
{
    /* Zero the kernel root page table */
    for (int i = 0; i < ENTRIES_PER_TABLE; i++)
        kernel_root_table.entries[i] = 0;

    /*
     * Identity-map the first 64 MB (covers kernel, UART, PLIC, CLINT).
     * QEMU virt RAM starts at 0x80000000, but we also need device MMIO.
     * Map 0x00000000..0x04000000 for device MMIO.
     * Map 0x80000000..0x84000000 for kernel RAM.
     */
    paging_identity_map_range(0x00000000, 0x04000000, PTE_KERN_RW);
    paging_identity_map_range(0x80000000, 0x84000000, PTE_KERN_RW);

    /* Enable Sv32 paging */
    mmu_enable((uint32_t)&kernel_root_table);
}

/* ── Map a single 4 KB page ──────────────────────────────────────────── */

void paging_map(uint32_t virt, uint32_t phys, uint32_t flags)
{
    uint32_t idx1 = vpn1(virt);
    uint32_t idx0 = vpn0(virt);

    page_table_t *leaf;

    if (kernel_root_table.entries[idx1] & PTE_V) {
        /* Leaf table already exists */
        uint32_t leaf_phys = pte_to_phys(kernel_root_table.entries[idx1]);
        leaf = (page_table_t *)leaf_phys;
    } else {
        /* Allocate a new leaf table */
        leaf = alloc_page_table();
        if (!leaf)
            return;  /* Pool exhausted */

        /* Non-leaf PTE: V bit set, no R/W/X (pointer to next level) */
        kernel_root_table.entries[idx1] = phys_to_pte((uint32_t)leaf, PTE_V);
    }

    /* Leaf PTE: set all requested flags + Valid */
    leaf->entries[idx0] = phys_to_pte(phys, flags | PTE_V);

    /* Flush the TLB entry for this virtual address */
    mmu_flush_tlb_page(virt);
}

/* ── Unmap a single 4 KB page ────────────────────────────────────────── */

void paging_unmap(uint32_t virt)
{
    uint32_t idx1 = vpn1(virt);
    uint32_t idx0 = vpn0(virt);

    if (!(kernel_root_table.entries[idx1] & PTE_V))
        return;

    uint32_t leaf_phys = pte_to_phys(kernel_root_table.entries[idx1]);
    page_table_t *leaf = (page_table_t *)leaf_phys;

    leaf->entries[idx0] = 0;
    mmu_flush_tlb_page(virt);
}

/* ── Walk page tables to translate virtual -> physical ───────────────── */

uint32_t paging_translate(uint32_t virt)
{
    uint32_t idx1 = vpn1(virt);
    uint32_t idx0 = vpn0(virt);

    if (!(kernel_root_table.entries[idx1] & PTE_V))
        return 0;  /* Not mapped */

    /* Check if this is a superpage (4 MB) */
    uint32_t root_pte = kernel_root_table.entries[idx1];
    if (root_pte & (PTE_R | PTE_W | PTE_X)) {
        /* Superpage: PPN[1] from PTE, VPN[0] and offset from vaddr */
        uint32_t base = (pte_to_ppn(root_pte) >> 10) << 22;
        return base | (virt & 0x003FFFFF);
    }

    uint32_t leaf_phys = pte_to_phys(root_pte);
    page_table_t *leaf = (page_table_t *)leaf_phys;

    if (!(leaf->entries[idx0] & PTE_V))
        return 0;  /* Not mapped */

    return pte_to_phys(leaf->entries[idx0]) | (virt & 0xFFF);
}

/* ── Identity-map a range of pages ───────────────────────────────────── */

void paging_identity_map_range(uint32_t start, uint32_t end, uint32_t flags)
{
    /* Align start down to page boundary */
    start &= ~(PAGE_SIZE - 1);

    for (uint32_t addr = start; addr < end; addr += PAGE_SIZE) {
        paging_map(addr, addr, flags);
    }
}

/* ── Accessor ────────────────────────────────────────────────────────── */

page_table_t *paging_get_root_table(void)
{
    return &kernel_root_table;
}
