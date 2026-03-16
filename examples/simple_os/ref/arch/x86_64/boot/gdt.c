/*
 * gdt.c — 64-bit Global Descriptor Table for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/boot/gdt.h"

/* ── Static data ───────────────────────────────────────────────────── */

/* 7 slots: 5 normal entries + 1 TSS64 entry (occupies 2 slots) */
static gdt_entry_t gdt_entries[GDT_NUM_ENTRIES];
static gdt_ptr64_t gdt_pointer;
static tss64_t     tss;

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

static void gdt_set_tss64(int idx, uint64_t base, uint32_t limit)
{
    gdt_tss64_entry_t *tss_entry = (gdt_tss64_entry_t *)&gdt_entries[idx];

    tss_entry->limit_low   = (uint16_t)(limit & 0xFFFF);
    tss_entry->base_low    = (uint16_t)(base & 0xFFFF);
    tss_entry->base_mid    = (uint8_t)((base >> 16) & 0xFF);
    tss_entry->access      = 0x89;      /* Present, 64-bit TSS (Available) */
    tss_entry->granularity = (uint8_t)(((limit >> 16) & 0x0F) | 0x00);
    tss_entry->base_high   = (uint8_t)((base >> 24) & 0xFF);
    tss_entry->base_upper  = (uint32_t)((base >> 32) & 0xFFFFFFFF);
    tss_entry->reserved    = 0;
}

/* ── Flush: load GDTR, reload segment registers, load TR ───────────── */

static inline void gdt_flush(void)
{
    __asm__ volatile (
        "lgdt (%0)\n\t"

        /* Reload CS via far return */
        "pushq %1\n\t"         /* Push new CS */
        "leaq 1f(%%rip), %%rax\n\t"
        "pushq %%rax\n\t"      /* Push return address */
        "lretq\n\t"            /* Far return to reload CS */
        "1:\n\t"

        /* Reload data segment registers */
        "movw %2, %%ax\n\t"
        "movw %%ax, %%ds\n\t"
        "movw %%ax, %%es\n\t"
        "movw %%ax, %%fs\n\t"
        "movw %%ax, %%gs\n\t"
        "movw %%ax, %%ss\n\t"
        :
        : "r"(&gdt_pointer),
          "i"((uint64_t)GDT_KERNEL_CODE64_SEG),
          "i"(GDT_KERNEL_DATA64_SEG)
        : "rax", "memory"
    );
}

static inline void tss_flush(void)
{
    __asm__ volatile (
        "movw %0, %%ax\n\t"
        "ltr  %%ax\n\t"
        :
        : "i"(GDT_TSS64_SEG)
        : "rax"
    );
}

/* ── Public API ────────────────────────────────────────────────────── */

void gdt_init(void)
{
    /* Clear TSS */
    uint8_t *tss_bytes = (uint8_t *)&tss;
    for (uint32_t i = 0; i < sizeof(tss); i++)
        tss_bytes[i] = 0;

    tss.rsp0 = 0;  /* Will be set via gdt_set_kernel_stack() */
    tss.iomap_base = sizeof(tss);

    uint64_t tss_base  = (uint64_t)&tss;
    uint32_t tss_limit = sizeof(tss) - 1;

    /*
     * GDT layout (long mode):
     *   0x00 — Null segment
     *   0x08 — Kernel Code64 (ring 0, L=1 long mode, D=0)
     *   0x10 — Kernel Data64 (ring 0, read/write)
     *   0x18 — User Code64   (ring 3, L=1 long mode, D=0)
     *   0x20 — User Data64   (ring 3, read/write)
     *   0x28 — TSS64         (16-byte system descriptor)
     *
     * In long mode, the base and limit fields of code/data segments
     * are ignored (flat addressing), but L=1 + D=0 is required for
     * 64-bit code segments.
     */
    gdt_set_entry(0, 0, 0,          0x00, 0x00);  /* Null         */
    gdt_set_entry(1, 0, 0xFFFFF,    0x9A, 0xA0);  /* Kernel Code64: L=1,D=0 */
    gdt_set_entry(2, 0, 0xFFFFF,    0x92, 0xC0);  /* Kernel Data64          */
    gdt_set_entry(3, 0, 0xFFFFF,    0xFA, 0xA0);  /* User Code64:   L=1,D=0 */
    gdt_set_entry(4, 0, 0xFFFFF,    0xF2, 0xC0);  /* User Data64            */
    gdt_set_tss64(5, tss_base, tss_limit);         /* TSS64 (slots 5+6)     */

    gdt_pointer.limit = (uint16_t)(sizeof(gdt_entries) - 1);
    gdt_pointer.base  = (uint64_t)&gdt_entries;

    gdt_flush();
    tss_flush();
}

void gdt_set_kernel_stack(uint64_t rsp)
{
    tss.rsp0 = rsp;
}

void gdt_set_ist(uint8_t ist_index, uint64_t stack)
{
    /* IST entries are 1-based (IST1..IST7) */
    switch (ist_index) {
        case 1: tss.ist1 = stack; break;
        case 2: tss.ist2 = stack; break;
        case 3: tss.ist3 = stack; break;
        case 4: tss.ist4 = stack; break;
        case 5: tss.ist5 = stack; break;
        case 6: tss.ist6 = stack; break;
        case 7: tss.ist7 = stack; break;
        default: break;
    }
}
