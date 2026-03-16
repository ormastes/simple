/*
 * isr_stubs.S — 64-bit ISR / IRQ stub assembly for x86_64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * In 64-bit mode: no pusha/popa, push individual registers,
 * 16-byte stack alignment, iretq.
 */

/* ══════════════════════════════════════════════════════════════════════
 * Macros
 * ══════════════════════════════════════════════════════════════════════ */

.macro ISR_NOERR num
    .global isr\num
    .type   isr\num, @function
    isr\num:
        pushq   $0
        pushq   $\num
        jmp     isr_common
.endm

.macro ISR_ERR num
    .global isr\num
    .type   isr\num, @function
    isr\num:
        pushq   $\num
        jmp     isr_common
.endm

.macro IRQ_STUB irq_num vec_num
    .global irq\irq_num
    .type   irq\irq_num, @function
    irq\irq_num:
        pushq   $0
        pushq   $\vec_num
        jmp     isr_common
.endm

/* ══════════════════════════════════════════════════════════════════════
 * CPU exceptions 0..31
 * ══════════════════════════════════════════════════════════════════════ */

ISR_NOERR  0
ISR_NOERR  1
ISR_NOERR  2
ISR_NOERR  3
ISR_NOERR  4
ISR_NOERR  5
ISR_NOERR  6
ISR_NOERR  7
ISR_ERR    8
ISR_NOERR  9
ISR_ERR   10
ISR_ERR   11
ISR_ERR   12
ISR_ERR   13
ISR_ERR   14
ISR_NOERR 15
ISR_NOERR 16
ISR_ERR   17
ISR_NOERR 18
ISR_NOERR 19
ISR_NOERR 20
ISR_ERR   21
ISR_NOERR 22
ISR_NOERR 23
ISR_NOERR 24
ISR_NOERR 25
ISR_NOERR 26
ISR_NOERR 27
ISR_NOERR 28
ISR_ERR   29
ISR_ERR   30
ISR_NOERR 31

/* ══════════════════════════════════════════════════════════════════════
 * Hardware IRQs 0..15 (vectors 32..47)
 * ══════════════════════════════════════════════════════════════════════ */

IRQ_STUB  0, 32
IRQ_STUB  1, 33
IRQ_STUB  2, 34
IRQ_STUB  3, 35
IRQ_STUB  4, 36
IRQ_STUB  5, 37
IRQ_STUB  6, 38
IRQ_STUB  7, 39
IRQ_STUB  8, 40
IRQ_STUB  9, 41
IRQ_STUB 10, 42
IRQ_STUB 11, 43
IRQ_STUB 12, 44
IRQ_STUB 13, 45
IRQ_STUB 14, 46
IRQ_STUB 15, 47

/* ══════════════════════════════════════════════════════════════════════
 * Common ISR handler
 * ══════════════════════════════════════════════════════════════════════ */

.extern trap_handler

isr_common:
    pushq   %rax
    pushq   %rbx
    pushq   %rcx
    pushq   %rdx
    pushq   %rsi
    pushq   %rdi
    pushq   %rbp
    pushq   %r8
    pushq   %r9
    pushq   %r10
    pushq   %r11
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15

    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es

    movq    %rsp, %rdi
    call    trap_handler

    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %r11
    popq    %r10
    popq    %r9
    popq    %r8
    popq    %rbp
    popq    %rdi
    popq    %rsi
    popq    %rdx
    popq    %rcx
    popq    %rbx
    popq    %rax

    addq    $16, %rsp

    iretq

/* ══════════════════════════════════════════════════════════════════════
 * ISR table (64-bit addresses)
 * ══════════════════════════════════════════════════════════════════════ */

.section .rodata
.global isr_table
.type   isr_table, @object

isr_table:
    .quad isr0,  isr1,  isr2,  isr3,  isr4,  isr5,  isr6,  isr7
    .quad isr8,  isr9,  isr10, isr11, isr12, isr13, isr14, isr15
    .quad isr16, isr17, isr18, isr19, isr20, isr21, isr22, isr23
    .quad isr24, isr25, isr26, isr27, isr28, isr29, isr30, isr31

    .quad irq0,  irq1,  irq2,  irq3,  irq4,  irq5,  irq6,  irq7
    .quad irq8,  irq9,  irq10, irq11, irq12, irq13, irq14, irq15

    .fill 208, 8, 0

.size isr_table, . - isr_table
