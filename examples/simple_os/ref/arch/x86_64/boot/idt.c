/*
 * idt.c — 64-bit Interrupt Descriptor Table for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/boot/idt.h"
#include "arch/x86_64/boot/gdt.h"

/* ── Static data ───────────────────────────────────────────────────── */

static idt_entry64_t idt_entries[IDT_NUM_ENTRIES];
static idt_ptr64_t   idt_pointer;

/* ── Set a single IDT gate (16-byte entry) ─────────────────────────── */

void idt_set_gate64(uint8_t num, uint64_t handler, uint16_t selector,
                    uint8_t ist, uint8_t type_attr)
{
    idt_entries[num].offset_low  = (uint16_t)(handler & 0xFFFF);
    idt_entries[num].offset_mid  = (uint16_t)((handler >> 16) & 0xFFFF);
    idt_entries[num].offset_high = (uint32_t)((handler >> 32) & 0xFFFFFFFF);
    idt_entries[num].selector    = selector;
    idt_entries[num].ist         = ist & 0x07;
    idt_entries[num].type_attr   = type_attr;
    idt_entries[num].reserved    = 0;
}

/* ── Load IDT register ─────────────────────────────────────────────── */

static inline void idt_flush(void)
{
    __asm__ volatile ("lidt (%0)" : : "r"(&idt_pointer) : "memory");
}

/* ── Public API ────────────────────────────────────────────────────── */

void idt_init(void)
{
    idt_pointer.limit = (uint16_t)(sizeof(idt_entries) - 1);
    idt_pointer.base  = (uint64_t)&idt_entries;

    /* Zero all entries */
    for (int i = 0; i < IDT_NUM_ENTRIES; i++) {
        idt_set_gate64((uint8_t)i, 0, 0, 0, 0);
    }

    /* CPU exceptions (vectors 0..31) — IST=0, interrupt gate */
    idt_set_gate64(0,  (uint64_t)isr0,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(1,  (uint64_t)isr1,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(2,  (uint64_t)isr2,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(3,  (uint64_t)isr3,  GDT_KERNEL_CODE64_SEG, 0, TRAP_GATE_64);
    idt_set_gate64(4,  (uint64_t)isr4,  GDT_KERNEL_CODE64_SEG, 0, TRAP_GATE_64);
    idt_set_gate64(5,  (uint64_t)isr5,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(6,  (uint64_t)isr6,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(7,  (uint64_t)isr7,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    /* Double fault uses IST1 for a clean stack */
    idt_set_gate64(8,  (uint64_t)isr8,  GDT_KERNEL_CODE64_SEG, 1, INTERRUPT_GATE_64);
    idt_set_gate64(9,  (uint64_t)isr9,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(10, (uint64_t)isr10, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(11, (uint64_t)isr11, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(12, (uint64_t)isr12, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(13, (uint64_t)isr13, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(14, (uint64_t)isr14, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(15, (uint64_t)isr15, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(16, (uint64_t)isr16, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(17, (uint64_t)isr17, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(18, (uint64_t)isr18, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(19, (uint64_t)isr19, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(20, (uint64_t)isr20, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(21, (uint64_t)isr21, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(22, (uint64_t)isr22, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(23, (uint64_t)isr23, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(24, (uint64_t)isr24, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(25, (uint64_t)isr25, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(26, (uint64_t)isr26, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(27, (uint64_t)isr27, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(28, (uint64_t)isr28, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(29, (uint64_t)isr29, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(30, (uint64_t)isr30, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(31, (uint64_t)isr31, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);

    /* Hardware IRQs (vectors 32..47) */
    idt_set_gate64(32, (uint64_t)irq0,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(33, (uint64_t)irq1,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(34, (uint64_t)irq2,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(35, (uint64_t)irq3,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(36, (uint64_t)irq4,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(37, (uint64_t)irq5,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(38, (uint64_t)irq6,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(39, (uint64_t)irq7,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(40, (uint64_t)irq8,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(41, (uint64_t)irq9,  GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(42, (uint64_t)irq10, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(43, (uint64_t)irq11, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(44, (uint64_t)irq12, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(45, (uint64_t)irq13, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(46, (uint64_t)irq14, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);
    idt_set_gate64(47, (uint64_t)irq15, GDT_KERNEL_CODE64_SEG, 0, INTERRUPT_GATE_64);

    /* Note: syscall in x86_64 uses SYSCALL/SYSRET via MSRs, not int 0x80.
     * No syscall gate in the IDT. */

    idt_flush();
}
