/*
 * crt0.s -- ARM32 (ARMv7) startup for QEMU virt
 *
 * Sets up stack, zeroes BSS, then calls _start (C entry point).
 * Runs in Supervisor mode (SVC).
 */

    .section .text.entry, "ax", %progbits
    .arm
    .globl _entry_asm
    .type _entry_asm, @function

_entry_asm:
    /* Disable interrupts (IRQ + FIQ) */
    cpsid if

    /* Set up stack pointer from linker symbol */
    ldr sp, =_stack_top

    /* Zero BSS section */
    ldr r0, =__bss_start
    ldr r1, =__bss_end
    mov r2, #0
1:
    cmp r0, r1
    strlt r2, [r0], #4
    blt 1b

    /* Call C _start */
    bl _start

    /* Halt: infinite WFE loop */
2:
    wfe
    b 2b

    .size _entry_asm, . - _entry_asm
