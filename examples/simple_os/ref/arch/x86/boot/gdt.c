/*
 * gdt.c — Global Descriptor Table for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86/boot/gdt.h"

/* ── Static data ───────────────────────────────────────────────────── */

static gdt_entry_t gdt_entries[GDT_NUM_ENTRIES];
static gdt_ptr_t   gdt_pointer;
static tss_t       tss;

/* ── Helpers ───────────────────────────────────────────────────────── */

static void gdt_set_entry(int idx, uint32_t base, uint32_t limit,
                          uint8_t access, uint8_t granularity)
{
    gdt_entries[idx].base_low    = (uint16_t)(base & 0xFFFF);
    gdt_entries[idx].base_mid    = (uint8_t)((base >> 16) & 0xFF);
    gdt_entries[idx].base_high   = (uint8_t)((base >> 24) & 0xFF);
    gdt_entries[idx].limit_low   = (uint16_t)(limit & 0xFFFF);
    gdt_entries[idx].granularity = (uint8_t)(((limit >> 16) & 0x0F) | (granularity & 0xF0));
    gdt_entries[idx].access      = access;
}

/* ── Flush: load GDTR, reload segment registers, load TR ───────────── */

static inline void gdt_flush(uint32_t gdt_ptr_addr)
{
    __asm__ volatile (
        "lgdt (%0)\n\t"

        /* Far jump to reload CS with kernel code selector */
        "ljmp %1, $1f\n\t"
        "1:\n\t"

        /* Reload data segment registers */
        "movw %2, %%ax\n\t"
        "movw %%ax, %%ds\n\t"
        "movw %%ax, %%es\n\t"
        "movw %%ax, %%fs\n\t"
        "movw %%ax, %%gs\n\t"
        "movw %%ax, %%ss\n\t"
        :
        : "r"(gdt_ptr_addr),
          "i"(GDT_KERNEL_CODE_SEG),
          "i"(GDT_KERNEL_DATA_SEG)
        : "eax", "memory"
    );
}

static inline void tss_flush(void)
{
    __asm__ volatile (
        "movw %0, %%ax\n\t"
        "ltr  %%ax\n\t"
        :
        : "i"(GDT_TSS_SEG)
        : "eax"
    );
}

/* ── Public API ────────────────────────────────────────────────────── */

void gdt_init(void)
{
    /* Clear TSS */
    for (uint32_t i = 0; i < sizeof(tss); i++)
        ((uint8_t *)&tss)[i] = 0;

    tss.ss0 = GDT_KERNEL_DATA_SEG;
    tss.esp0 = 0;  /* Will be set via gdt_set_kernel_stack() */
    tss.iomap_base = sizeof(tss);

    uint32_t tss_base  = (uint32_t)&tss;
    uint32_t tss_limit = sizeof(tss) - 1;

    /*
     * GDT layout:
     *   0x00 — Null segment
     *   0x08 — Kernel Code  (ring 0, execute/read, 4GB flat)
     *   0x10 — Kernel Data  (ring 0, read/write, 4GB flat)
     *   0x18 — User Code    (ring 3, execute/read, 4GB flat)
     *   0x20 — User Data    (ring 3, read/write, 4GB flat)
     *   0x28 — TSS
     */
    gdt_set_entry(0, 0, 0,          0x00, 0x00);  /* Null         */
    gdt_set_entry(1, 0, 0xFFFFFFFF, 0x9A, 0xCF);  /* Kernel Code  */
    gdt_set_entry(2, 0, 0xFFFFFFFF, 0x92, 0xCF);  /* Kernel Data  */
    gdt_set_entry(3, 0, 0xFFFFFFFF, 0xFA, 0xCF);  /* User Code    */
    gdt_set_entry(4, 0, 0xFFFFFFFF, 0xF2, 0xCF);  /* User Data    */
    gdt_set_entry(5, tss_base, tss_limit, 0x89, 0x40);  /* TSS    */

    gdt_pointer.limit = (uint16_t)(sizeof(gdt_entries) - 1);
    gdt_pointer.base  = (uint32_t)&gdt_entries;

    gdt_flush((uint32_t)&gdt_pointer);
    tss_flush();
}

void gdt_set_kernel_stack(uint32_t esp)
{
    tss.esp0 = esp;
}
