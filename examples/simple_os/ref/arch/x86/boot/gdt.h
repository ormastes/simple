/*
 * gdt.h — Global Descriptor Table for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_BOOT_GDT_H
#define ARCH_X86_BOOT_GDT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── GDT segment selectors ─────────────────────────────────────────── */

#define GDT_NULL_SEG        0x00
#define GDT_KERNEL_CODE_SEG 0x08
#define GDT_KERNEL_DATA_SEG 0x10
#define GDT_USER_CODE_SEG   0x18
#define GDT_USER_DATA_SEG   0x20
#define GDT_TSS_SEG         0x28

#define GDT_NUM_ENTRIES     6

/* ── GDT entry (8 bytes, packed) ───────────────────────────────────── */

typedef struct PACKED {
    uint16_t limit_low;     /* Lower 16 bits of the limit          */
    uint16_t base_low;      /* Lower 16 bits of the base           */
    uint8_t  base_mid;      /* Bits 16..23 of the base             */
    uint8_t  access;        /* Access byte                         */
    uint8_t  granularity;   /* Flags + upper 4 bits of limit       */
    uint8_t  base_high;     /* Bits 24..31 of the base             */
} gdt_entry_t;

/* ── GDT pointer (for lgdt) ────────────────────────────────────────── */

typedef struct PACKED {
    uint16_t limit;
    uint32_t base;
} gdt_ptr_t;

/* ── TSS (Task State Segment, 104 bytes) ───────────────────────────── */

typedef struct PACKED {
    uint32_t prev_task;
    uint32_t esp0;          /* Kernel stack pointer                */
    uint32_t ss0;           /* Kernel stack segment                */
    uint32_t esp1;
    uint32_t ss1;
    uint32_t esp2;
    uint32_t ss2;
    uint32_t cr3;
    uint32_t eip;
    uint32_t eflags;
    uint32_t eax;
    uint32_t ecx;
    uint32_t edx;
    uint32_t ebx;
    uint32_t esp;
    uint32_t ebp;
    uint32_t esi;
    uint32_t edi;
    uint32_t es;
    uint32_t cs;
    uint32_t ss;
    uint32_t ds;
    uint32_t fs;
    uint32_t gs;
    uint32_t ldt;
    uint16_t trap;
    uint16_t iomap_base;
} tss_t;

/* ── Public API ────────────────────────────────────────────────────── */

void gdt_init(void);
void gdt_set_kernel_stack(uint32_t esp);

#endif /* ARCH_X86_BOOT_GDT_H */
