/*
 * idt.c — Interrupt Descriptor Table for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86/boot/idt.h"
#include "arch/x86/boot/gdt.h"

/* ── Static data ───────────────────────────────────────────────────── */

static idt_entry_t idt_entries[IDT_NUM_ENTRIES];
static idt_ptr_t   idt_pointer;

/* ── Set a single IDT gate ─────────────────────────────────────────── */

void idt_set_gate(uint8_t num, uint32_t handler, uint16_t selector,
                  uint8_t type_attr)
{
    idt_entries[num].offset_low  = (uint16_t)(handler & 0xFFFF);
    idt_entries[num].offset_high = (uint16_t)((handler >> 16) & 0xFFFF);
    idt_entries[num].selector    = selector;
    idt_entries[num].zero        = 0;
    idt_entries[num].type_attr   = type_attr;
}

/* ── Load IDT register ─────────────────────────────────────────────── */

static inline void idt_flush(uint32_t idt_ptr_addr)
{
    __asm__ volatile ("lidt (%0)" : : "r"(idt_ptr_addr) : "memory");
}

/* ── Public API ────────────────────────────────────────────────────── */

void idt_init(void)
{
    idt_pointer.limit = (uint16_t)(sizeof(idt_entries) - 1);
    idt_pointer.base  = (uint32_t)&idt_entries;

    /* Zero all entries */
    for (int i = 0; i < IDT_NUM_ENTRIES; i++) {
        idt_set_gate((uint8_t)i, 0, 0, 0);
    }

    /* CPU exceptions (vectors 0..31) */
    idt_set_gate(0,  (uint32_t)isr0,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(1,  (uint32_t)isr1,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(2,  (uint32_t)isr2,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(3,  (uint32_t)isr3,  GDT_KERNEL_CODE_SEG, TRAP_GATE);
    idt_set_gate(4,  (uint32_t)isr4,  GDT_KERNEL_CODE_SEG, TRAP_GATE);
    idt_set_gate(5,  (uint32_t)isr5,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(6,  (uint32_t)isr6,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(7,  (uint32_t)isr7,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(8,  (uint32_t)isr8,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(9,  (uint32_t)isr9,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(10, (uint32_t)isr10, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(11, (uint32_t)isr11, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(12, (uint32_t)isr12, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(13, (uint32_t)isr13, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(14, (uint32_t)isr14, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(15, (uint32_t)isr15, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(16, (uint32_t)isr16, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(17, (uint32_t)isr17, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(18, (uint32_t)isr18, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(19, (uint32_t)isr19, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(20, (uint32_t)isr20, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(21, (uint32_t)isr21, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(22, (uint32_t)isr22, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(23, (uint32_t)isr23, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(24, (uint32_t)isr24, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(25, (uint32_t)isr25, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(26, (uint32_t)isr26, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(27, (uint32_t)isr27, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(28, (uint32_t)isr28, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(29, (uint32_t)isr29, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(30, (uint32_t)isr30, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(31, (uint32_t)isr31, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);

    /* Hardware IRQs (vectors 32..47) */
    idt_set_gate(32, (uint32_t)irq0,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(33, (uint32_t)irq1,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(34, (uint32_t)irq2,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(35, (uint32_t)irq3,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(36, (uint32_t)irq4,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(37, (uint32_t)irq5,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(38, (uint32_t)irq6,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(39, (uint32_t)irq7,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(40, (uint32_t)irq8,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(41, (uint32_t)irq9,  GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(42, (uint32_t)irq10, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(43, (uint32_t)irq11, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(44, (uint32_t)irq12, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(45, (uint32_t)irq13, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(46, (uint32_t)irq14, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);
    idt_set_gate(47, (uint32_t)irq15, GDT_KERNEL_CODE_SEG, INTERRUPT_GATE);

    /* Syscall gate (vector 0x80) — DPL=3 so user-mode can invoke */
    idt_set_gate(0x80, (uint32_t)syscall_entry, GDT_KERNEL_CODE_SEG,
                 SYSCALL_GATE);

    idt_flush((uint32_t)&idt_pointer);
}
