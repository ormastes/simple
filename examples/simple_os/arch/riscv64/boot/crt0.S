/*
 * crt0.S -- RISC-V 64 S-mode startup (with OpenSBI)
 *
 * OpenSBI boots the kernel in S-mode at 0x80200000.
 * Sets up stack, zeroes BSS, then calls spl_start (Simple entry point).
 *
 * Uses S-mode CSRs (sstatus) — OpenSBI provides the M-mode runtime.
 */

    .section .text.entry, "ax", @progbits
    .globl _start
    .type _start, @function

_start:
    /* Disable S-mode interrupts: clear SIE bit in sstatus */
    csrci   sstatus, 0x2

    /* Set up stack pointer from linker symbol */
    la      sp, _stack_top

    /* Zero BSS section */
    la      t0, _sbss
    la      t1, _ebss
.Lbss_loop:
    bge     t0, t1, .Lbss_done
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       .Lbss_loop
.Lbss_done:

    /* Call Simple entry point */
    call    spl_start

    /* Halt: infinite WFI loop */
.Lhalt:
    wfi
    j       .Lhalt

    .size _start, . - _start
