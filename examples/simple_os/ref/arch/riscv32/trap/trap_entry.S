/*
 * trap_entry.S — Trap vector entry/exit for RISC-V32 (M-mode)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Saves all 31 general-purpose registers (x1..x31) plus mepc, mstatus,
 * mcause, and mtval onto the stack as a trap_frame_t, then calls the
 * C trap_handler(). On return, restores all registers and executes mret.
 *
 * trap_frame_t layout (32 GP regs + 4 CSRs = 36 words = 144 bytes):
 *   sp+0:   ra (x1)
 *   sp+4:   sp (x2)  — saved original sp
 *   sp+8:   gp (x3)
 *   sp+12:  tp (x4)
 *   sp+16:  t0 (x5)
 *   sp+20:  t1 (x6)
 *   sp+24:  t2 (x7)
 *   sp+28:  s0 (x8)
 *   sp+32:  s1 (x9)
 *   sp+36:  a0 (x10)
 *   sp+40:  a1 (x11)
 *   sp+44:  a2 (x12)
 *   sp+48:  a3 (x13)
 *   sp+52:  a4 (x14)
 *   sp+56:  a5 (x15)
 *   sp+60:  a6 (x16)
 *   sp+64:  a7 (x17)
 *   sp+68:  s2 (x18)
 *   sp+72:  s3 (x19)
 *   sp+76:  s4 (x20)
 *   sp+80:  s5 (x21)
 *   sp+84:  s6 (x22)
 *   sp+88:  s7 (x23)
 *   sp+92:  s8 (x24)
 *   sp+96:  s9 (x25)
 *   sp+100: s10 (x26)
 *   sp+104: s11 (x27)
 *   sp+108: t3 (x28)
 *   sp+112: t4 (x29)
 *   sp+116: t5 (x30)
 *   sp+120: t6 (x31)
 *   sp+124: mepc
 *   sp+128: mstatus
 *   sp+132: mcause
 *   sp+136: mtval
 */

.section .text
.global trap_entry
.type   trap_entry, @function
.align 4

trap_entry:
    /* ── Allocate trap frame on stack (140 bytes = 35 words) ── */
    /* We save 31 GP regs + 4 CSRs = 35 words, but sp is saved separately */
    /* Total frame: 36 words = 144 bytes */
    addi    sp, sp, -144

    /* ── Save general-purpose registers ── */
    sw      ra,   0(sp)     /* x1  */
    /* x2 (sp) saved below after we compute the original value */
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

    /* Save original sp (before the addi -144) */
    addi    t0, sp, 144
    sw      t0,   4(sp)    /* x2 (original sp) */

    /* ── Save CSRs ── */
    csrr    t0, mepc
    sw      t0, 124(sp)
    csrr    t0, mstatus
    sw      t0, 128(sp)
    csrr    t0, mcause
    sw      t0, 132(sp)
    csrr    t0, mtval
    sw      t0, 136(sp)

    /* ── Call C trap handler ── */
    /* a0 = pointer to trap_frame_t (current sp) */
    mv      a0, sp
    call    trap_handler

    /* ── Restore CSRs ── */
    lw      t0, 124(sp)
    csrw    mepc, t0
    lw      t0, 128(sp)
    csrw    mstatus, t0
    /* mcause and mtval are read-only from software perspective */

    /* ── Restore general-purpose registers ── */
    lw      ra,   0(sp)     /* x1  */
    /* x2 (sp) restored last */
    lw      gp,   8(sp)     /* x3  */
    lw      tp,  12(sp)     /* x4  */
    lw      t0,  16(sp)     /* x5  */
    lw      t1,  20(sp)     /* x6  */
    lw      t2,  24(sp)     /* x7  */
    lw      s0,  28(sp)     /* x8  */
    lw      s1,  32(sp)     /* x9  */
    lw      a0,  36(sp)     /* x10 */
    lw      a1,  40(sp)     /* x11 */
    lw      a2,  44(sp)     /* x12 */
    lw      a3,  48(sp)     /* x13 */
    lw      a4,  52(sp)     /* x14 */
    lw      a5,  56(sp)     /* x15 */
    lw      a6,  60(sp)     /* x16 */
    lw      a7,  64(sp)     /* x17 */
    lw      s2,  68(sp)     /* x18 */
    lw      s3,  72(sp)     /* x19 */
    lw      s4,  76(sp)     /* x20 */
    lw      s5,  80(sp)     /* x21 */
    lw      s6,  84(sp)     /* x22 */
    lw      s7,  88(sp)     /* x23 */
    lw      s8,  92(sp)     /* x24 */
    lw      s9,  96(sp)     /* x25 */
    lw      s10,100(sp)     /* x26 */
    lw      s11,104(sp)     /* x27 */
    lw      t3, 108(sp)     /* x28 */
    lw      t4, 112(sp)     /* x29 */
    lw      t5, 116(sp)     /* x30 */
    lw      t6, 120(sp)     /* x31 */

    /* Restore stack pointer */
    addi    sp, sp, 144

    /* Return from trap */
    mret

.size trap_entry, . - trap_entry
