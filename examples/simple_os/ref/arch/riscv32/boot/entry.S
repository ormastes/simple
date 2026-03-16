/*
 * entry.S — M-mode boot entry point for RISC-V32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * QEMU virt starts execution at 0x80000000 in M-mode.
 * This entry point:
 *   1. Sets up the initial stack pointer
 *   2. Zeros the BSS section
 *   3. Sets the trap vector (mtvec)
 *   4. Enables M-mode interrupts in mstatus
 *   5. Calls kernel_main()
 *   6. Loops in wfi if kernel_main returns
 */

.section .text.init, "ax"
.global _start
.type   _start, @function

_start:
    /* ── Only allow hart 0 to proceed; park other harts ── */
    csrr    t0, mhartid
    bnez    t0, .park_hart

    /* ── Set up the stack pointer ── */
    la      sp, _stack_top

    /* ── Zero the BSS section ── */
    la      t0, _bss_start
    la      t1, _bss_end
.bss_loop:
    bge     t0, t1, .bss_done
    sw      zero, 0(t0)
    addi    t0, t0, 4
    j       .bss_loop
.bss_done:

    /* ── Set the trap vector (mtvec) ── */
    /*
     * Use direct mode (LSB = 0): all traps go to trap_entry.
     * trap_entry is defined in trap/trap_entry.S
     */
    la      t0, trap_entry
    csrw    mtvec, t0

    /* ── Configure mstatus ── */
    /*
     * Set MIE (Machine Interrupt Enable) bit in mstatus.
     * mstatus.MIE = bit 3
     * Also set MPIE (bit 7) so interrupts are re-enabled on mret.
     */
    li      t0, (1 << 3) | (1 << 7)
    csrw    mstatus, t0

    /* ── Enable machine interrupts in mie ── */
    /*
     * MIE register bits:
     *   bit 3: MSIE (Software Interrupt Enable)
     *   bit 7: MTIE (Timer Interrupt Enable)
     *   bit 11: MEIE (External Interrupt Enable)
     */
    li      t0, (1 << 3) | (1 << 7) | (1 << 11)
    csrw    mie, t0

    /* ── Call kernel_main() ── */
    call    kernel_main

    /* ── Halt loop if kernel_main returns ── */
.halt_loop:
    wfi
    j       .halt_loop

    /* ── Park non-zero harts in wfi loop ── */
.park_hart:
    wfi
    j       .park_hart

.size _start, . - _start
