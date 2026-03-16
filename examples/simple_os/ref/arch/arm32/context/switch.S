/*
 * switch.S — Context switch assembly for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *
 * context_t layout (offsets in bytes):
 *    0: r0     44: r11 (fp)
 *    4: r1     48: r12 (ip)
 *    8: r2     52: sp
 *   12: r3     56: lr
 *   16: r4     60: pc
 *   20: r5     64: cpsr
 *   24: r6
 *   28: r7
 *   32: r8
 *   36: r9
 *   40: r10
 */

/* Field offsets in context_t */
.set CTX_R0,    0
.set CTX_R1,    4
.set CTX_R2,    8
.set CTX_R3,    12
.set CTX_R4,    16
.set CTX_R5,    20
.set CTX_R6,    24
.set CTX_R7,    28
.set CTX_R8,    32
.set CTX_R9,    36
.set CTX_R10,   40
.set CTX_R11,   44
.set CTX_R12,   48
.set CTX_SP,    52
.set CTX_LR,    56
.set CTX_PC,    60
.set CTX_CPSR,  64

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context_t *old, context_t *new)
 *
 * Save callee-saved registers (r4-r11, sp, lr) into *old,
 * then load them from *new and branch to new->pc.
 *
 * r0 = old context pointer
 * r1 = new context pointer
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, %function

context_switch:
    /* ── Save current state into old context ── */

    /* Save callee-saved registers */
    str     r4,  [r0, #CTX_R4]
    str     r5,  [r0, #CTX_R5]
    str     r6,  [r0, #CTX_R6]
    str     r7,  [r0, #CTX_R7]
    str     r8,  [r0, #CTX_R8]
    str     r9,  [r0, #CTX_R9]
    str     r10, [r0, #CTX_R10]
    str     r11, [r0, #CTX_R11]
    str     r12, [r0, #CTX_R12]

    /* Save SP and LR */
    str     sp,  [r0, #CTX_SP]
    str     lr,  [r0, #CTX_LR]

    /* Save return address as PC (LR = address after bl context_switch) */
    str     lr,  [r0, #CTX_PC]

    /* Save CPSR */
    mrs     r2, cpsr
    str     r2,  [r0, #CTX_CPSR]

    /* ── Load state from new context ── */

    /* Load CPSR (into SPSR so it takes effect on return) */
    ldr     r2,  [r1, #CTX_CPSR]
    msr     spsr_cxsf, r2

    /* Load callee-saved registers */
    ldr     r4,  [r1, #CTX_R4]
    ldr     r5,  [r1, #CTX_R5]
    ldr     r6,  [r1, #CTX_R6]
    ldr     r7,  [r1, #CTX_R7]
    ldr     r8,  [r1, #CTX_R8]
    ldr     r9,  [r1, #CTX_R9]
    ldr     r10, [r1, #CTX_R10]
    ldr     r11, [r1, #CTX_R11]
    ldr     r12, [r1, #CTX_R12]

    /* Load SP */
    ldr     sp,  [r1, #CTX_SP]

    /* Load LR */
    ldr     lr,  [r1, #CTX_LR]

    /* Branch to the new context's PC */
    ldr     pc,  [r1, #CTX_PC]

.size context_switch, . - context_switch
