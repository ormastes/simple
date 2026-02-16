/*
 * Simple Seed — Baremetal RISC-V 32 (RV32) _start
 *
 * No OS — 32-bit RISC-V entry point.
 * Sets up stack and jumps to C startup.
 * Expects to be loaded at a known address (e.g., by SBI or bootloader).
 *
 * Linker script must define __bss_start and __bss_end.
 */

    .section .text
    .global _start
    .type _start, @function

    .align 2

_start:
    /* Disable interrupts */
    csrci   mstatus, 0x8           /* Clear MIE bit */

    /* Set up stack (grows downward) */
    la      sp, __spl_stack_top

    /* Clear frame pointer and return address */
    li      s0, 0
    li      ra, 0

    /* Call C startup — zeros BSS, then calls main */
    call    __spl_start_bare

    /* Should never return — __spl_exit halts the CPU */
1:  wfi
    j       1b

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
