/*
 * switch.S — Context switch assembly for AArch64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *   x0 = old context pointer
 *   x1 = new context pointer
 *
 * We save/restore only callee-saved registers (x19-x30, sp)
 * since the C/Simple ABI guarantees caller saves the rest.
 *
 * RegisterState layout (offsets for callee-saved):
 *   x19 at offset 152 (19 * 8)
 *   x20 at offset 160
 *   ...
 *   x29 at offset 232 (FP)
 *   x30 at offset 240 (LR)
 *   sp  at offset 248
 */

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
.set CTX_FP,    232
.set CTX_LR,    240
.set CTX_SP,    248

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* Save callee-saved registers into old context */
    stp     x19, x20, [x0, #CTX_X19]
    stp     x21, x22, [x0, #CTX_X21]
    stp     x23, x24, [x0, #CTX_X23]
    stp     x25, x26, [x0, #CTX_X25]
    stp     x27, x28, [x0, #CTX_X27]
    stp     x29, x30, [x0, #CTX_FP]
    mov     x2, sp
    str     x2, [x0, #CTX_SP]

    /* Load callee-saved registers from new context */
    ldp     x19, x20, [x1, #CTX_X19]
    ldp     x21, x22, [x1, #CTX_X21]
    ldp     x23, x24, [x1, #CTX_X23]
    ldp     x25, x26, [x1, #CTX_X25]
    ldp     x27, x28, [x1, #CTX_X27]
    ldp     x29, x30, [x1, #CTX_FP]
    ldr     x2, [x1, #CTX_SP]
    mov     sp, x2

    /* Return to new context via LR (x30) */
    ret

.size context_switch, . - context_switch
