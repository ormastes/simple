/*
 * crt0.S -- RISC-V 32 M-mode startup (no OpenSBI)
 *
 * Direct M-mode boot for QEMU virt with -bios none.
 * Sets up stack, zeroes BSS, then calls spl_start (Simple entry point).
 *
 * Uses M-mode CSRs (mstatus) — NOT S-mode (sstatus).
 */

    .section .text.entry, "ax", @progbits
    .globl _start
    .type _start, @function

_start:
    /* Disable M-mode interrupts: clear MIE bit in mstatus */
    csrci   mstatus, 0x8

    /* Set up stack pointer from linker symbol */
    la      sp, _stack_top

    /* Zero BSS section */
    la      t0, _sbss
    la      t1, _ebss
.Lbss_loop:
    bge     t0, t1, .Lbss_done
    sw      zero, 0(t0)
    addi    t0, t0, 4
    j       .Lbss_loop
.Lbss_done:

    /* Call Simple entry point */
    call    spl_start

    /* Halt: infinite WFI loop */
.Lhalt:
    wfi
    j       .Lhalt

    .size _start, . - _start
