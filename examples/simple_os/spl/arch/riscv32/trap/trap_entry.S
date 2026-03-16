/*
 * trap_entry.S — Trap vector entry/exit for RISC-V32 (M-mode)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Saves all 31 general-purpose registers (x1..x31) plus mepc, mstatus,
 * mcause, and mtval onto the stack as a TrapFrame, then calls the
 * Simple trap_handler(). On return, restores all registers and mret.
 *
 * Frame size: 36 words = 144 bytes (31 GP regs + sp + 4 CSRs)
 */

.section .text
.global trap_entry
.type   trap_entry, @function
.align 4

trap_entry:
    /* Allocate trap frame: 36 words = 144 bytes */
    addi    sp, sp, -144

    /* Save general-purpose registers */
    sw      ra,   0(sp)     /* x1  */
    /* sp (x2) saved below */
    sw      gp,   8(sp)     /* x3  */
    sw      tp,  12(sp)     /* x4  */
    sw      t0,  16(sp)     /* x5  */
    sw      t1,  20(sp)     /* x6  */
    sw      t2,  24(sp)     /* x7  */
    sw      s0,  28(sp)     /* x8  */
    sw      s1,  32(sp)     /* x9  */
    sw      a0,  36(sp)     /* x10 */
    sw      a1,  40(sp)     /* x11 */
    sw      a2,  44(sp)     /* x12 */
    sw      a3,  48(sp)     /* x13 */
    sw      a4,  52(sp)     /* x14 */
    sw      a5,  56(sp)     /* x15 */
    sw      a6,  60(sp)     /* x16 */
    sw      a7,  64(sp)     /* x17 */
    sw      s2,  68(sp)     /* x18 */
    sw      s3,  72(sp)     /* x19 */
    sw      s4,  76(sp)     /* x20 */
    sw      s5,  80(sp)     /* x21 */
    sw      s6,  84(sp)     /* x22 */
    sw      s7,  88(sp)     /* x23 */
    sw      s8,  92(sp)     /* x24 */
    sw      s9,  96(sp)     /* x25 */
    sw      s10,100(sp)     /* x26 */
    sw      s11,104(sp)     /* x27 */
    sw      t3, 108(sp)     /* x28 */
    sw      t4, 112(sp)     /* x29 */
    sw      t5, 116(sp)     /* x30 */
    sw      t6, 120(sp)     /* x31 */

    /* Save original sp (before addi -144) */
    addi    t0, sp, 144
    sw      t0,   4(sp)    /* x2 */

    /* Save CSRs */
    csrr    t0, mepc
    sw      t0, 124(sp)
    csrr    t0, mstatus
    sw      t0, 128(sp)
    csrr    t0, mcause
    sw      t0, 132(sp)
    csrr    t0, mtval
    sw      t0, 136(sp)

    /* Call trap_handler(frame: TrapFrame) */
    mv      a0, sp
    call    trap_handler

    /* Restore CSRs */
    lw      t0, 124(sp)
    csrw    mepc, t0
    lw      t0, 128(sp)
    csrw    mstatus, t0

    /* Restore general-purpose registers */
    lw      ra,   0(sp)
    lw      gp,   8(sp)
    lw      tp,  12(sp)
    lw      t0,  16(sp)
    lw      t1,  20(sp)
    lw      t2,  24(sp)
    lw      s0,  28(sp)
    lw      s1,  32(sp)
    lw      a0,  36(sp)
    lw      a1,  40(sp)
    lw      a2,  44(sp)
    lw      a3,  48(sp)
    lw      a4,  52(sp)
    lw      a5,  56(sp)
    lw      a6,  60(sp)
    lw      a7,  64(sp)
    lw      s2,  68(sp)
    lw      s3,  72(sp)
    lw      s4,  76(sp)
    lw      s5,  80(sp)
    lw      s6,  84(sp)
    lw      s7,  88(sp)
    lw      s8,  92(sp)
    lw      s9,  96(sp)
    lw      s10,100(sp)
    lw      s11,104(sp)
    lw      t3, 108(sp)
    lw      t4, 112(sp)
    lw      t5, 116(sp)
    lw      t6, 120(sp)

    /* Restore stack pointer */
    addi    sp, sp, 144

    /* Return from trap */
    mret

.size trap_entry, . - trap_entry
