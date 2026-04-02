/*
 * crt0.S -- ARM64 (AArch64) startup for QEMU virt
 *
 * Sets up stack, zeroes BSS, then calls spl_start (Simple entry point).
 * Runs at EL1 (or EL2 if QEMU drops us there — we don't switch).
 */

    .section .text.entry, "ax", %progbits
    .globl _start
    .type _start, @function

_start:
    /* Set up stack pointer from linker symbol */
    adrp    x0, _stack_top
    add     sp, x0, :lo12:_stack_top

    /* Zero BSS section */
    adrp    x0, _sbss
    add     x0, x0, :lo12:_sbss
    adrp    x1, _ebss
    add     x1, x1, :lo12:_ebss
.Lbss_loop:
    cmp     x0, x1
    b.ge    .Lbss_done
    str     xzr, [x0], #8
    b       .Lbss_loop
.Lbss_done:

    /* Call Simple entry point */
    bl      spl_start

    /* Halt: infinite WFE loop */
.Lhalt:
    wfe
    b       .Lhalt

    .size _start, . - _start
