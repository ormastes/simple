/*
 * Simple Seed — Baremetal x86 (i386) _start
 *
 * No OS — 32-bit protected mode entry.
 * Sets up stack and jumps to C startup.
 *
 * Linker script must define __bss_start and __bss_end.
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    cli

    /* Set up stack */
    mov     $__spl_stack_top, %esp
    xor     %ebp, %ebp

    call    __spl_start_bare

    cli
1:  hlt
    jmp     1b

    .size _start, . - _start

/*
 * Stack: 64KB in .bss
 */
    .section .bss
    .align 16
__spl_stack_bottom:
    .space 65536
    .global __spl_stack_top
__spl_stack_top:
