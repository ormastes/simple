/*
 * Simple Seed — Baremetal ARM32 _start
 *
 * No OS — 32-bit ARM entry point.
 * Sets up stack and jumps to C startup.
 * Expects to be loaded at a known address (e.g., by bootloader).
 *
 * Linker script must define __bss_start and __bss_end.
 */

    .section .text
    .global _start
    .type _start, %function

    .arm

_start:
    /* Disable IRQ and FIQ */
    cpsid   if

    /* Set up stack (grows downward) */
    ldr     sp, =__spl_stack_top

    /* Clear frame pointer */
    mov     fp, #0

    /* Call C startup — zeros BSS, then calls main */
    bl      __spl_start_bare

    /* Should never return — __spl_exit halts the CPU */
    cpsid   if
1:  wfi
    b       1b

    .size _start, . - _start

/*
 * Stack: 64KB in .bss (zeroed by __spl_start_bare -> __spl_zero_bss)
 */
    .section .bss
    .align 4
__spl_stack_bottom:
    .space 65536
    .global __spl_stack_top
__spl_stack_top:
