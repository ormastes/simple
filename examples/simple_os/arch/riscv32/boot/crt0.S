/*
 * crt0.S -- RISC-V 32 M-mode startup (no OpenSBI)
 *
 * Direct M-mode boot for QEMU virt with -bios none.
 * Sets up stack, zeroes BSS, installs M-mode trap handler for ecall
 * dispatch, then calls spl_start (Simple entry point).
 *
 * Uses M-mode CSRs (mstatus, mtvec, mepc, mcause) — NOT S-mode.
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

    /* Install M-mode trap handler for ecall dispatch */
    la      t0, _mmode_trap_handler
    csrw    mtvec, t0

    /* Initialize UART and print boot banner before entering Simple code */
    call    _boot_init

    /* Call Simple entry point */
    call    spl_start

    /* QEMU virt finisher success exit when spl_start returns */
    li      t0, 0x100000
    li      t1, 0x5555
    sw      t1, 0(t0)

    /* Fallback halt if the finisher is unavailable */
.Lhalt:
    wfi
    j       .Lhalt

    .size _start, . - _start

/* =========================================================================
 * M-mode trap handler
 *
 * Handles ecall from M-mode (mcause=11) by dispatching to the C syscall
 * function. The Simple compiler emits `ecall` for syscalls even in M-mode
 * (there's no SBI firmware), so we handle it here.
 *
 * On entry: a7 = syscall ID, a0-a4 = args (set by Simple's inline asm)
 * On exit:  a0 = result (from C handler), mepc advanced by 4
 * ========================================================================= */

    .section .text.trap, "ax", @progbits
    .balign 4
    .globl _mmode_trap_handler
    .type _mmode_trap_handler, @function

_mmode_trap_handler:
    /* Save registers we'll clobber on the current stack.
     * We use mscratch to save/restore sp if needed, but since we're
     * already in M-mode with the kernel stack, just use sp directly. */

    addi    sp, sp, -80
    sw      ra,  0(sp)
    sw      t0,  4(sp)
    sw      t1,  8(sp)
    sw      t2, 12(sp)
    sw      a0, 16(sp)
    sw      a1, 20(sp)
    sw      a2, 24(sp)
    sw      a3, 28(sp)
    sw      a4, 32(sp)
    sw      a5, 36(sp)
    sw      a6, 40(sp)
    sw      a7, 44(sp)
    sw      t3, 48(sp)
    sw      t4, 52(sp)
    sw      t5, 56(sp)
    sw      t6, 60(sp)
    sw      s0, 64(sp)
    sw      s1, 68(sp)

    /* Check mcause: 11 = ecall from M-mode */
    csrr    t0, mcause
    li      t1, 11
    bne     t0, t1, .Ltrap_other

    /* Ecall from M-mode: dispatch to C syscall handler.
     * C ABI: args in a0-a5 for userlib__syscall_raw__syscall(id, a0, a1, a2, a3, a4)
     * But on RV32 with uint64_t params, each arg takes 2 registers.
     * Our C function takes uint64_t args, so we need to pass them as
     * 64-bit values. The Simple ecall puts 32-bit values in a0-a4, a7.
     *
     * Simpler approach: call a 32-bit wrapper that takes uint32_t args. */

    /* Load saved a7 (syscall ID) and a0-a4 (args) from stack */
    lw      a0, 44(sp)    /* a7 = syscall ID -> first arg */
    lw      a1, 16(sp)    /* a0 = arg0 -> second arg */
    lw      a2, 20(sp)    /* a1 = arg1 -> third arg */
    lw      a3, 24(sp)    /* a2 = arg2 -> fourth arg */
    lw      a4, 28(sp)    /* a3 = arg3 -> fifth arg */
    lw      a5, 32(sp)    /* a4 = arg4 -> sixth arg */

    /* Call C handler: int32_t _trap_syscall(uint32_t id, uint32_t a0, ..., uint32_t a4) */
    call    _trap_syscall

    /* Result is in a0 (int32_t). Store it back so the caller sees it.
     * On RV32, int64_t return values use register pair (a0=low, a1=high).
     * Sign-extend a0 into a1 for correct 64-bit result. */
    sw      a0, 16(sp)     /* overwrite saved a0 with result (low word) */
    srai    a0, a0, 31     /* sign-extend: all 1s if negative, all 0s if positive */
    sw      a0, 20(sp)     /* overwrite saved a1 with sign extension (high word) */

    /* Advance mepc past the ecall instruction (4 bytes) */
    csrr    t0, mepc
    addi    t0, t0, 4
    csrw    mepc, t0

    j       .Ltrap_return

.Ltrap_other:
    /* Non-ecall trap: advance mepc by 4 to skip the faulting instruction.
     * This is a coarse workaround — illegal instructions, alignment faults,
     * etc. are silently skipped. For a production OS we'd decode mcause
     * and handle properly. */
    csrr    t0, mepc
    addi    t0, t0, 4
    csrw    mepc, t0

.Ltrap_return:
    /* Restore registers */
    lw      ra,  0(sp)
    lw      t0,  4(sp)
    lw      t1,  8(sp)
    lw      t2, 12(sp)
    lw      a0, 16(sp)
    lw      a1, 20(sp)
    lw      a2, 24(sp)
    lw      a3, 28(sp)
    lw      a4, 32(sp)
    lw      a5, 36(sp)
    lw      a6, 40(sp)
    lw      a7, 44(sp)
    lw      t3, 48(sp)
    lw      t4, 52(sp)
    lw      t5, 56(sp)
    lw      t6, 60(sp)
    lw      s0, 64(sp)
    lw      s1, 68(sp)
    addi    sp, sp, 80

    mret

    .size _mmode_trap_handler, . - _mmode_trap_handler
