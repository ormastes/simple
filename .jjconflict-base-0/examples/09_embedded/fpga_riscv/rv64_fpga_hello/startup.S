/* startup.S — RV64 bare-metal FPGA startup
 *
 * Runs at reset vector (0x80000000 for DDR boot).
 * Sets sp, clears BSS, calls main, then halts with wfi.
 * Trap vector points to a single-instruction halt (j .).
 */

    .option norvc          /* disable compressed insns for entry section */
    .section .text.entry
    .globl _start
    .type  _start, @function

_start:
    /* ------------------------------------------------------------------ */
    /* 1. Install minimal trap vector (bare address mode, mtvec.MODE=0)    */
    /* ------------------------------------------------------------------ */
    la      t0, _trap_halt
    csrw    mtvec, t0

    /* ------------------------------------------------------------------ */
    /* 2. Set stack pointer to top of reserved stack region                */
    /* ------------------------------------------------------------------ */
    la      sp, _stack_top

    /* ------------------------------------------------------------------ */
    /* 3. Zero .bss                                                        */
    /* ------------------------------------------------------------------ */
    la      t0, _bss_start
    la      t1, _bss_end
.Lclear_bss:
    bgeu    t0, t1, .Lbss_done
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       .Lclear_bss
.Lbss_done:

    /* ------------------------------------------------------------------ */
    /* 4. Call main (hart 0 only; additional harts sleep)                  */
    /* ------------------------------------------------------------------ */
    csrr    a0, mhartid
    bnez    a0, .Lhalt          /* non-zero hart: park immediately */

    li      a0, 0               /* argc = 0 */
    li      a1, 0               /* argv = NULL */
    call    main

    /* ------------------------------------------------------------------ */
    /* 5. Infinite halt on return                                           */
    /* ------------------------------------------------------------------ */
.Lhalt:
    wfi
    j       .Lhalt

    /* ------------------------------------------------------------------ */
    /* Trap vector — any exception/interrupt lands here and halts          */
    /* ------------------------------------------------------------------ */
    .align 4
    .globl _trap_halt
    .type  _trap_halt, @function
_trap_halt:
    wfi
    j       _trap_halt

    .size _start, . - _start
