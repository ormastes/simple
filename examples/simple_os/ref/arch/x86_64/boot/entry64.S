/*
 * entry64.S — 64-bit entry point for x86_64 kernel
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Called from boot_wrapper.S after the 32→64 mode switch.
 * This code runs in 64-bit long mode with identity-mapped first 4 MB.
 *
 * Responsibilities:
 *   1. Reload 64-bit data segments
 *   2. Set up the 64-bit kernel stack
 *   3. Zero BSS
 *   4. Call kernel_main
 */

.section .text
.code64
.global _start64
.type _start64, @function

_start64:
    /* Reload data segments with 64-bit data selector */
    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs
    movw    %ax, %ss

    /* Set up the 64-bit kernel stack */
    movabs  $_stack_top, %rsp

    /* ── Zero the BSS section (64-bit) ────────────────────────── */
    movabs  $_bss_start, %rdi
    movabs  $_bss_end, %rcx
    subq    %rdi, %rcx
    shrq    $3, %rcx            /* count in 64-bit words */
    xorq    %rax, %rax
    rep stosq

    /* RDI = 0 (no multiboot info in two-stage boot) */
    xorq    %rdi, %rdi

    /* Call the 64-bit kernel entry point */
    call    kernel_main

    /* If kernel_main returns, halt the CPU */
.halt_loop:
    cli
    hlt
    jmp     .halt_loop

.size _start64, . - _start64
