/*
 * switch.S — Context switch assembly for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *
 * context_t layout (offsets in bytes, 8 bytes per field):
 *    0: ra     8: sp    16: s0    24: s1
 *   32: s2    40: s3    48: s4    56: s5
 *   64: s6    72: s7    80: s8    88: s9
 *   96: s10  104: s11  112: a0   120: a1
 *  128: a2   136: a3   144: a4   152: a5
 *  160: a6   168: a7   176: tp   184: gp
 *  192: mstatus  200: mepc
 */

/* Field offsets in context_t */
.set CTX_RA,       0
.set CTX_SP,       8
.set CTX_S0,      16
.set CTX_S1,      24
.set CTX_S2,      32
.set CTX_S3,      40
.set CTX_S4,      48
.set CTX_S5,      56
.set CTX_S6,      64
.set CTX_S7,      72
.set CTX_S8,      80
.set CTX_S9,      88
.set CTX_S10,     96
.set CTX_S11,    104
.set CTX_A0,     112
.set CTX_A1,     120
.set CTX_A2,     128
.set CTX_A3,     136
.set CTX_A4,     144
.set CTX_A5,     152
.set CTX_A6,     160
.set CTX_A7,     168
.set CTX_TP,     176
.set CTX_GP,     184
.set CTX_MSTATUS,192
.set CTX_MEPC,   200

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context_t *old, context_t *new)
 *   a0 = old context pointer
 *   a1 = new context pointer
 *
 * Save callee-saved registers (s0-s11, ra, sp) into *old,
 * then load them from *new and return to new->ra.
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* ── Save current state into old context (a0) ── */

    sd      ra,  CTX_RA(a0)
    sd      sp,  CTX_SP(a0)
    sd      s0,  CTX_S0(a0)
    sd      s1,  CTX_S1(a0)
    sd      s2,  CTX_S2(a0)
    sd      s3,  CTX_S3(a0)
    sd      s4,  CTX_S4(a0)
    sd      s5,  CTX_S5(a0)
    sd      s6,  CTX_S6(a0)
    sd      s7,  CTX_S7(a0)
    sd      s8,  CTX_S8(a0)
    sd      s9,  CTX_S9(a0)
    sd      s10, CTX_S10(a0)
    sd      s11, CTX_S11(a0)

    /* ── Load state from new context (a1) ── */

    ld      ra,  CTX_RA(a1)
    ld      sp,  CTX_SP(a1)
    ld      s0,  CTX_S0(a1)
    ld      s1,  CTX_S1(a1)
    ld      s2,  CTX_S2(a1)
    ld      s3,  CTX_S3(a1)
    ld      s4,  CTX_S4(a1)
    ld      s5,  CTX_S5(a1)
    ld      s6,  CTX_S6(a1)
    ld      s7,  CTX_S7(a1)
    ld      s8,  CTX_S8(a1)
    ld      s9,  CTX_S9(a1)
    ld      s10, CTX_S10(a1)
    ld      s11, CTX_S11(a1)

    /* Return to new context's return address */
    ret

.size context_switch, . - context_switch
