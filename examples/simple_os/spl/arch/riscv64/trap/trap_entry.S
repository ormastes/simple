/*
 * trap_entry.S — 64-bit trap vector for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation (Simple).
 *
 * Saves all 31 general-purpose registers (x1-x31) + CSRs into a
 * TrapFrame on the stack, calls the Simple trap_handler, restores, mret.
 *
 * TrapFrame layout (offsets in bytes, 8 bytes per register):
 *    0: ra(x1)   8: sp(x2)   16: gp(x3)   24: tp(x4)
 *   32: t0(x5)  40: t1(x6)   48: t2(x7)   56: s0(x8)
 *   64: s1(x9)  72: a0(x10)  80: a1(x11)  88: a2(x12)
 *   96: a3(x13) 104: a4(x14) 112: a5(x15) 120: a6(x16)
 *  128: a7(x17) 136: s2(x18) 144: s3(x19) 152: s4(x20)
 *  160: s5(x21) 168: s6(x22) 176: s7(x23) 184: s8(x24)
 *  192: s9(x25) 200: s10(x26) 208: s11(x27) 216: t3(x28)
 *  224: t4(x29) 232: t5(x30)  240: t6(x31)
 *  248: mepc   256: mstatus  264: mcause   272: mtval
 */

/* Frame size: 31 GPRs * 8 + 4 CSRs * 8 = 280 bytes, aligned to 16 */
.set FRAME_SIZE, 280

/* GPR offsets */
.set OFF_RA,     0
.set OFF_SP,     8
.set OFF_GP,    16
.set OFF_TP,    24
.set OFF_T0,    32
.set OFF_T1,    40
.set OFF_T2,    48
.set OFF_S0,    56
.set OFF_S1,    64
.set OFF_A0,    72
.set OFF_A1,    80
.set OFF_A2,    88
.set OFF_A3,    96
.set OFF_A4,   104
.set OFF_A5,   112
.set OFF_A6,   120
.set OFF_A7,   128
.set OFF_S2,   136
.set OFF_S3,   144
.set OFF_S4,   152
.set OFF_S5,   160
.set OFF_S6,   168
.set OFF_S7,   176
.set OFF_S8,   184
.set OFF_S9,   192
.set OFF_S10,  200
.set OFF_S11,  208
.set OFF_T3,   216
.set OFF_T4,   224
.set OFF_T5,   232
.set OFF_T6,   240

/* CSR offsets */
.set OFF_MEPC,    248
.set OFF_MSTATUS, 256
.set OFF_MCAUSE,  264
.set OFF_MTVAL,   272

/* ══════════════════════════════════════════════════════════════════════
 * Trap entry point (set as mtvec, direct mode)
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global trap_entry
.type   trap_entry, @function
.align 4

trap_entry:
    /* Allocate trap frame on stack */
    addi    sp, sp, -FRAME_SIZE

    /* Save all general-purpose registers (x1-x31) */
    sd      ra,  OFF_RA(sp)
    /* sp saved below after we compute original sp */
    sd      gp,  OFF_GP(sp)
    sd      tp,  OFF_TP(sp)
    sd      t0,  OFF_T0(sp)
    sd      t1,  OFF_T1(sp)
    sd      t2,  OFF_T2(sp)
    sd      s0,  OFF_S0(sp)
    sd      s1,  OFF_S1(sp)
    sd      a0,  OFF_A0(sp)
    sd      a1,  OFF_A1(sp)
    sd      a2,  OFF_A2(sp)
    sd      a3,  OFF_A3(sp)
    sd      a4,  OFF_A4(sp)
    sd      a5,  OFF_A5(sp)
    sd      a6,  OFF_A6(sp)
    sd      a7,  OFF_A7(sp)
    sd      s2,  OFF_S2(sp)
    sd      s3,  OFF_S3(sp)
    sd      s4,  OFF_S4(sp)
    sd      s5,  OFF_S5(sp)
    sd      s6,  OFF_S6(sp)
    sd      s7,  OFF_S7(sp)
    sd      s8,  OFF_S8(sp)
    sd      s9,  OFF_S9(sp)
    sd      s10, OFF_S10(sp)
    sd      s11, OFF_S11(sp)
    sd      t3,  OFF_T3(sp)
    sd      t4,  OFF_T4(sp)
    sd      t5,  OFF_T5(sp)
    sd      t6,  OFF_T6(sp)

    /* Save original sp (before frame allocation) */
    addi    t0, sp, FRAME_SIZE
    sd      t0,  OFF_SP(sp)

    /* Save CSRs */
    csrr    t0, mepc
    sd      t0,  OFF_MEPC(sp)
    csrr    t0, mstatus
    sd      t0,  OFF_MSTATUS(sp)
    csrr    t0, mcause
    sd      t0,  OFF_MCAUSE(sp)
    csrr    t0, mtval
    sd      t0,  OFF_MTVAL(sp)

    /* Call Simple handler with pointer to trap frame */
    mv      a0, sp
    call    trap_handler

    /* Restore CSRs */
    ld      t0,  OFF_MEPC(sp)
    csrw    mepc, t0
    ld      t0,  OFF_MSTATUS(sp)
    csrw    mstatus, t0

    /* Restore general-purpose registers */
    ld      ra,  OFF_RA(sp)
    /* sp restored last */
    ld      gp,  OFF_GP(sp)
    ld      tp,  OFF_TP(sp)
    ld      t0,  OFF_T0(sp)
    ld      t1,  OFF_T1(sp)
    ld      t2,  OFF_T2(sp)
    ld      s0,  OFF_S0(sp)
    ld      s1,  OFF_S1(sp)
    ld      a0,  OFF_A0(sp)
    ld      a1,  OFF_A1(sp)
    ld      a2,  OFF_A2(sp)
    ld      a3,  OFF_A3(sp)
    ld      a4,  OFF_A4(sp)
    ld      a5,  OFF_A5(sp)
    ld      a6,  OFF_A6(sp)
    ld      a7,  OFF_A7(sp)
    ld      s2,  OFF_S2(sp)
    ld      s3,  OFF_S3(sp)
    ld      s4,  OFF_S4(sp)
    ld      s5,  OFF_S5(sp)
    ld      s6,  OFF_S6(sp)
    ld      s7,  OFF_S7(sp)
    ld      s8,  OFF_S8(sp)
    ld      s9,  OFF_S9(sp)
    ld      s10, OFF_S10(sp)
    ld      s11, OFF_S11(sp)
    ld      t3,  OFF_T3(sp)
    ld      t4,  OFF_T4(sp)
    ld      t5,  OFF_T5(sp)
    ld      t6,  OFF_T6(sp)

    /* Restore stack pointer (deallocate frame) */
    addi    sp, sp, FRAME_SIZE

    /* Return from machine-mode trap */
    mret

.size trap_entry, . - trap_entry
