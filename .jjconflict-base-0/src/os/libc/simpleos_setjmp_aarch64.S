/*
 * SimpleOS setjmp/longjmp — aarch64 assembly
 *
 * jmp_buf layout (24 x u64, see include/setjmp.h aarch64 branch):
 *   [0..9]   x19-x28   callee-saved GPRs
 *   [10]     x29 (fp)
 *   [11]     x30 (lr)  — resume PC
 *   [12]     sp
 *   [13..20] d8-d15    callee-saved FP regs (AAPCS64)
 *   [21..23] reserved
 */

.section .text

.global setjmp
.type setjmp, @function
setjmp:
    stp     x19, x20, [x0, #0]
    stp     x21, x22, [x0, #16]
    stp     x23, x24, [x0, #32]
    stp     x25, x26, [x0, #48]
    stp     x27, x28, [x0, #64]
    stp     x29, x30, [x0, #80]
    mov     x9, sp
    str     x9,       [x0, #96]
    stp     d8,  d9,  [x0, #104]
    stp     d10, d11, [x0, #120]
    stp     d12, d13, [x0, #136]
    stp     d14, d15, [x0, #152]
    mov     w0, wzr
    ret
.size setjmp, . - setjmp

.global _setjmp
.type _setjmp, @function
_setjmp:
    b       setjmp
.size _setjmp, . - _setjmp

.global longjmp
.type longjmp, @function
longjmp:
    ldp     x19, x20, [x0, #0]
    ldp     x21, x22, [x0, #16]
    ldp     x23, x24, [x0, #32]
    ldp     x25, x26, [x0, #48]
    ldp     x27, x28, [x0, #64]
    ldp     x29, x30, [x0, #80]
    ldr     x9,       [x0, #96]
    mov     sp, x9
    ldp     d8,  d9,  [x0, #104]
    ldp     d10, d11, [x0, #120]
    ldp     d12, d13, [x0, #136]
    ldp     d14, d15, [x0, #152]
    /* return val, forcing 1 when val == 0 (C standard) */
    cmp     w1, wzr
    csinc   w0, w1, wzr, ne
    ret
.size longjmp, . - longjmp

.global _longjmp
.type _longjmp, @function
_longjmp:
    b       longjmp
.size _longjmp, . - _longjmp
