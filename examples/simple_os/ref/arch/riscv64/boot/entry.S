/*
 * entry.S — M-mode boot entry point for RISC-V 64-bit (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * _start: set sp (64-bit), zero BSS, set mtvec, call kernel_main, wfi loop.
 * Uses 64-bit instructions (ld/sd instead of lw/sw).
 */

/* ── Stack size ───────────────────────────────────────────────────── */

.set STACK_SIZE, 16384   /* 16 KB */

/* ══════════════════════════════════════════════════════════════════════
 * Entry point
 * ══════════════════════════════════════════════════════════════════════ */

.section .text.entry
.global _start
.type _start, @function

_start:
    /* Disable all interrupts until kernel is ready */
    csrw    mstatus, zero
    csrw    mie, zero

    /* Read hart ID; only hart 0 boots, others park */
    csrr    t0, mhartid
    bnez    t0, .park

    /* Set up the initial kernel stack (64-bit pointer) */
    la      sp, _stack_top

    /* Zero the BSS section */
    la      t0, _bss_start
    la      t1, _bss_end
.zero_bss:
    beq     t0, t1, .bss_done
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       .zero_bss
.bss_done:

    /* Set up machine trap vector (direct mode) */
    la      t0, trap_entry
    csrw    mtvec, t0

    /* NOTE: Interrupts remain disabled (mstatus.MIE=0, mie=0).
     * kernel_main will enable them once handlers are installed. */

    /* Pass hart_id = 0 as first argument */
    li      a0, 0

    /* Call the C/Simple kernel entry point */
    call    kernel_main

    /* If kernel_main returns, halt */
.park:
    wfi
    j       .park

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Stack reservation
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss
.align 16

_stack_bottom:
    .space STACK_SIZE
_stack_top:
