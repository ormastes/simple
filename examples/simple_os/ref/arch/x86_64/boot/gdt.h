/*
 * gdt.h — 64-bit Global Descriptor Table for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * GDT layout for long mode:
 *   0x00 — Null
 *   0x08 — Kernel Code64  (L=1, D=0)
 *   0x10 — Kernel Data64
 *   0x18 — User Code64    (DPL=3, L=1)
 *   0x20 — User Data64    (DPL=3)
 *   0x28 — TSS64          (16-byte system descriptor)
 */

#ifndef ARCH_X86_64_BOOT_GDT_H
#define ARCH_X86_64_BOOT_GDT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── GDT segment selectors ─────────────────────────────────────────── */

#define GDT_NULL_SEG            0x00
#define GDT_KERNEL_CODE64_SEG   0x08
#define GDT_KERNEL_DATA64_SEG   0x10
#define GDT_USER_CODE64_SEG     0x18    /* RPL=3: 0x18 | 3 = 0x1B */
#define GDT_USER_DATA64_SEG     0x20    /* RPL=3: 0x20 | 3 = 0x23 */
#define GDT_TSS64_SEG           0x28

/* Number of 8-byte slots (TSS64 uses 2 slots = 16 bytes) */
#define GDT_NUM_ENTRIES         7

/* ── Standard GDT entry (8 bytes, packed) ──────────────────────────── */

typedef struct PACKED {
    uint16_t limit_low;     /* Lower 16 bits of the limit          */
    uint16_t base_low;      /* Lower 16 bits of the base           */
    uint8_t  base_mid;      /* Bits 16..23 of the base             */
    uint8_t  access;        /* Access byte                         */
    uint8_t  granularity;   /* Flags + upper 4 bits of limit       */
    uint8_t  base_high;     /* Bits 24..31 of the base             */
} gdt_entry_t;

/* ── TSS64 descriptor (16 bytes: two consecutive gdt_entry_t slots) ── */

typedef struct PACKED {
    uint16_t limit_low;
    uint16_t base_low;
    uint8_t  base_mid;
    uint8_t  access;
    uint8_t  granularity;
    uint8_t  base_high;
    uint32_t base_upper;    /* Bits 32..63 of the base             */
    uint32_t reserved;
} gdt_tss64_entry_t;

/* ── GDT pointer (for lgdt in 64-bit mode) ─────────────────────────── */

typedef struct PACKED {
    uint16_t limit;
    uint64_t base;
} gdt_ptr64_t;

/* ── TSS64 (104 bytes + IST entries) ───────────────────────────────── */

typedef struct PACKED {
    uint32_t reserved0;
    uint64_t rsp0;          /* Kernel stack for ring 0             */
    uint64_t rsp1;          /* Stack for ring 1 (unused)           */
    uint64_t rsp2;          /* Stack for ring 2 (unused)           */
    uint64_t reserved1;
    uint64_t ist1;          /* Interrupt Stack Table entries 1-7   */
    uint64_t ist2;
    uint64_t ist3;
    uint64_t ist4;
    uint64_t ist5;
    uint64_t ist6;
    uint64_t ist7;
    uint64_t reserved2;
    uint16_t reserved3;
    uint16_t iomap_base;
} tss64_t;

/* ── Public API ────────────────────────────────────────────────────── */

void gdt_init(void);
void gdt_set_kernel_stack(uint64_t rsp);
void gdt_set_ist(uint8_t ist_index, uint64_t stack);

#endif /* ARCH_X86_64_BOOT_GDT_H */
