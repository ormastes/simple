/*
 * Simple Seed — Baremetal x86_64 _start
 *
 * No OS — we set up our own stack and jump to C.
 * Expects to be loaded at a known address (e.g., by bootloader
 * or UEFI). Stack is allocated in .bss.
 *
 * Linker script must define __bss_start and __bss_end.
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    /* Disable interrupts until we're ready */
    cli

    /* Set up stack (grows downward) */
    lea     __spl_stack_top(%rip), %rsp
    xor     %rbp, %rbp

    /* Call C startup — zeros BSS, then calls main */
    call    __spl_start_bare

    /* Should never return — __spl_exit halts the CPU */
    cli
1:  hlt
    jmp     1b

    .size _start, . - _start

/*
 * Stack: 64KB in .bss (zeroed by __spl_start_bare -> __spl_zero_bss)
 */
    .section .bss
    .align 16
__spl_stack_bottom:
    .space 65536
    .global __spl_stack_top
__spl_stack_top:
