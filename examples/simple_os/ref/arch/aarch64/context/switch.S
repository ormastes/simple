/*
 * switch.S — Context switch assembly for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *
 * context_t layout (offsets in bytes):
 *     0: x[0]  (x0)
 *     8: x[1]  (x1)
 *   ...
 *   152: x[19]
 *   160: x[20]
 *   ...
 *   232: x[29] (FP)
 *   240: x[30] (LR)
 *   248: sp
 *   256: elr_el1
 *   264: spsr_el1
 *
 * We only save/restore callee-saved registers (x19-x30, sp)
 * since the C ABI guarantees the caller saves the rest.
 */

/* Field offsets */
.set CTX_X19,   152
.set CTX_X20,   160
.set CTX_X21,   168
.set CTX_X22,   176
.set CTX_X23,   184
.set CTX_X24,   192
.set CTX_X25,   200
.set CTX_X26,   208
.set CTX_X27,   216
.set CTX_X28,   224
.set CTX_FP,    232     /* x29 = frame pointer */
.set CTX_LR,    240     /* x30 = link register */
.set CTX_SP,    248

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context_t *old, context_t *new)
 *   x0 = old context pointer
 *   x1 = new context pointer
 *
 * Save callee-saved registers + SP into *old,
 * load them from *new and return (via LR).
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* ── Save current state into old context ── */

    /* Save callee-saved registers x19-x28 */
    stp     x19, x20, [x0, #CTX_X19]
    stp     x21, x22, [x0, #CTX_X21]
    stp     x23, x24, [x0, #CTX_X23]
    stp     x25, x26, [x0, #CTX_X25]
    stp     x27, x28, [x0, #CTX_X27]

    /* Save FP (x29) and LR (x30) */
    stp     x29, x30, [x0, #CTX_FP]

    /* Save SP */
    mov     x2, sp
    str     x2, [x0, #CTX_SP]

    /* ── Load state from new context ── */

    /* Load callee-saved registers x19-x28 */
    ldp     x19, x20, [x1, #CTX_X19]
    ldp     x21, x22, [x1, #CTX_X21]
    ldp     x23, x24, [x1, #CTX_X23]
    ldp     x25, x26, [x1, #CTX_X25]
    ldp     x27, x28, [x1, #CTX_X27]

    /* Load FP (x29) and LR (x30) */
    ldp     x29, x30, [x1, #CTX_FP]

    /* Load SP */
    ldr     x2, [x1, #CTX_SP]
    mov     sp, x2

    /* Return to the new context's LR */
    ret

.size context_switch, . - context_switch
