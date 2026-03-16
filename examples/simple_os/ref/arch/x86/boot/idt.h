/*
 * idt.h — Interrupt Descriptor Table for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_BOOT_IDT_H
#define ARCH_X86_BOOT_IDT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── IDT constants ─────────────────────────────────────────────────── */

#define IDT_NUM_ENTRIES     256

#define INTERRUPT_GATE      0x8E  /* P=1, DPL=0, 32-bit interrupt gate */
#define TRAP_GATE           0x8F  /* P=1, DPL=0, 32-bit trap gate      */
#define SYSCALL_GATE        0xEE  /* P=1, DPL=3, 32-bit interrupt gate */

/* ── IDT entry (8 bytes, packed) ───────────────────────────────────── */

typedef struct PACKED {
    uint16_t offset_low;    /* Lower 16 bits of handler address    */
    uint16_t selector;      /* Kernel code segment selector        */
    uint8_t  zero;          /* Always zero                         */
    uint8_t  type_attr;     /* Type and attributes                 */
    uint16_t offset_high;   /* Upper 16 bits of handler address    */
} idt_entry_t;

/* ── IDT pointer (for lidt) ────────────────────────────────────────── */

typedef struct PACKED {
    uint16_t limit;
    uint32_t base;
} idt_ptr_t;

/* ── External ISR stubs (defined in isr_stubs.S) ───────────────────── */

/* CPU exceptions 0..31 */
extern void isr0(void);
extern void isr1(void);
extern void isr2(void);
extern void isr3(void);
extern void isr4(void);
extern void isr5(void);
extern void isr6(void);
extern void isr7(void);
extern void isr8(void);
extern void isr9(void);
extern void isr10(void);
extern void isr11(void);
extern void isr12(void);
extern void isr13(void);
extern void isr14(void);
extern void isr15(void);
extern void isr16(void);
extern void isr17(void);
extern void isr18(void);
extern void isr19(void);
extern void isr20(void);
extern void isr21(void);
extern void isr22(void);
extern void isr23(void);
extern void isr24(void);
extern void isr25(void);
extern void isr26(void);
extern void isr27(void);
extern void isr28(void);
extern void isr29(void);
extern void isr30(void);
extern void isr31(void);

/* Hardware IRQs 0..15  (mapped to vectors 32..47) */
extern void irq0(void);
extern void irq1(void);
extern void irq2(void);
extern void irq3(void);
extern void irq4(void);
extern void irq5(void);
extern void irq6(void);
extern void irq7(void);
extern void irq8(void);
extern void irq9(void);
extern void irq10(void);
extern void irq11(void);
extern void irq12(void);
extern void irq13(void);
extern void irq14(void);
extern void irq15(void);

/* Syscall entry (vector 0x80) */
extern void syscall_entry(void);

/* ── Public API ────────────────────────────────────────────────────── */

void idt_init(void);
void idt_set_gate(uint8_t num, uint32_t handler, uint16_t selector,
                  uint8_t type_attr);

#endif /* ARCH_X86_BOOT_IDT_H */
