/*
 * switch.S — Context switch assembly for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *
 * context_t layout (offsets in bytes):
 *    0: ra    (x1)
 *    4: sp    (x2)
 *    8: s0    (x8)
 *   12: s1    (x9)
 *   16: s2    (x18)
 *   20: s3    (x19)
 *   24: s4    (x20)
 *   28: s5    (x21)
 *   32: s6    (x22)
 *   36: s7    (x23)
 *   40: s8    (x24)
 *   44: s9    (x25)
 *   48: s10   (x26)
 *   52: s11   (x27)
 *   56: a0    (x10)
 *   60: a1    (x11)
 *   64: mepc
 *   68: mstatus
 */

/* Field offsets in context_t */
.set CTX_RA,       0
.set CTX_SP,       4
.set CTX_S0,       8
.set CTX_S1,      12
.set CTX_S2,      16
.set CTX_S3,      20
.set CTX_S4,      24
.set CTX_S5,      28
.set CTX_S6,      32
.set CTX_S7,      36
.set CTX_S8,      40
.set CTX_S9,      44
.set CTX_S10,     48
.set CTX_S11,     52
.set CTX_A0,      56
.set CTX_A1,      60
.set CTX_MEPC,    64
.set CTX_MSTATUS, 68

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context_t *old, context_t *new)
 *
 * Save callee-saved registers into *old, load from *new, then ret.
 * Arguments: a0 = old context pointer, a1 = new context pointer
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* ── Save current state into old context ── */

    sw      ra,  CTX_RA(a0)
    sw      sp,  CTX_SP(a0)
    sw      s0,  CTX_S0(a0)
    sw      s1,  CTX_S1(a0)
    sw      s2,  CTX_S2(a0)
    sw      s3,  CTX_S3(a0)
    sw      s4,  CTX_S4(a0)
    sw      s5,  CTX_S5(a0)
    sw      s6,  CTX_S6(a0)
    sw      s7,  CTX_S7(a0)
    sw      s8,  CTX_S8(a0)
    sw      s9,  CTX_S9(a0)
    sw      s10, CTX_S10(a0)
    sw      s11, CTX_S11(a0)

    /* ── Load state from new context ── */

    lw      ra,  CTX_RA(a1)
    lw      sp,  CTX_SP(a1)
    lw      s0,  CTX_S0(a1)
    lw      s1,  CTX_S1(a1)
    lw      s2,  CTX_S2(a1)
    lw      s3,  CTX_S3(a1)
    lw      s4,  CTX_S4(a1)
    lw      s5,  CTX_S5(a1)
    lw      s6,  CTX_S6(a1)
    lw      s7,  CTX_S7(a1)
    lw      s8,  CTX_S8(a1)
    lw      s9,  CTX_S9(a1)
    lw      s10, CTX_S10(a1)
    lw      s11, CTX_S11(a1)

    /* Return to new context's ra */
    ret

.size context_switch, . - context_switch
