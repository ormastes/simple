/*
 * entry.S — M-mode boot entry point for RISC-V32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * QEMU virt starts execution at 0x80000000 in M-mode.
 * This entry point:
 *   1. Parks non-zero harts
 *   2. Sets up the initial stack pointer
 *   3. Zeros the BSS section
 *   4. Sets the trap vector (mtvec)
 *   5. Enables M-mode interrupts in mstatus
 *   6. Calls kernel_main()
 *   7. Loops in wfi if kernel_main returns
 */

.section .text.init, "ax"
.global _start
.type   _start, @function

_start:
    /* ── Disable all interrupts until kernel is ready ── */
    csrw    mstatus, zero
    csrw    mie, zero

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
    la      t0, trap_entry
    csrw    mtvec, t0

    /* NOTE: Interrupts remain disabled (mstatus.MIE=0, mie=0).
     * kernel_main will enable them once handlers are installed. */

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
