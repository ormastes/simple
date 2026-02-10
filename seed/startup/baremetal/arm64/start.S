/*
 * Simple Seed — Baremetal ARM64 (AArch64) _start
 *
 * No OS — 64-bit ARM entry point.
 * Sets up stack and jumps to C startup.
 * Expects to be loaded at a known address (e.g., by bootloader or UEFI).
 *
 * Linker script must define __bss_start and __bss_end.
 */

    .section .text
    .global _start
    .type _start, %function

    .p2align 2

_start:
    /* Disable interrupts (clear DAIF bits) */
    msr     daifset, #0xF

    /* Set up stack (grows downward) */
    adrp    x0, __spl_stack_top
    add     x0, x0, :lo12:__spl_stack_top
    mov     sp, x0

    /* Clear frame pointer */
    mov     x29, #0

    /* Call C startup — zeros BSS, then calls main */
    bl      __spl_start_bare

    /* Should never return — __spl_exit halts the CPU */
    msr     daifset, #0xF
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
