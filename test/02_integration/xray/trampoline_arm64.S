// Candidate pure-Simple Windows classic ARM64 tracing trampoline.
// Inline module assembly, emitted into COFF by unmodified LLVM 20.1.
// This code is only statically verified; no native ARM64 runtime was available.
// No SEH/unwind feature is required by Simple's chosen contract.

.text
.p2align 2

.macro SIMPLE_TRACE_TRAMP name, kind
.globl \name
\name:
    bti c
    pacibsp
    stp x29, x30, [sp, #-16]!
    mov x29, sp

    // Sled already saves/restores x0, x16, x17, and original x30.
    // Preserve every other volatile integer value before invoking C code.
    stp x1,  x2,  [sp, #-16]!
    stp x3,  x4,  [sp, #-16]!
    stp x5,  x6,  [sp, #-16]!
    stp x7,  x8,  [sp, #-16]!
    stp x9,  x10, [sp, #-16]!
    stp x11, x12, [sp, #-16]!
    stp x13, x14, [sp, #-16]!
    mrs x16, nzcv
    stp x15, x16, [sp, #-16]!

    // Full q registers: SIMD upper halves may be live at an inserted hook.
    sub sp, sp, #512
    stp q0,  q1,  [sp, #0]
    stp q2,  q3,  [sp, #32]
    stp q4,  q5,  [sp, #64]
    stp q6,  q7,  [sp, #96]
    stp q8,  q9,  [sp, #128]
    stp q10, q11, [sp, #160]
    stp q12, q13, [sp, #192]
    stp q14, q15, [sp, #224]
    stp q16, q17, [sp, #256]
    stp q18, q19, [sp, #288]
    stp q20, q21, [sp, #320]
    stp q22, q23, [sp, #352]
    stp q24, q25, [sp, #384]
    stp q26, q27, [sp, #416]
    stp q28, q29, [sp, #448]
    stp q30, q31, [sp, #480]

    mrs x16, fpcr
    mrs x17, fpsr
    stp x16, x17, [sp, #-16]!
    mov w1, #\kind
    // w0 already contains the function ID from the sled.
    bl simple_trace_dispatch

    ldp x16, x17, [sp], #16
    msr fpcr, x16
    msr fpsr, x17
    ldp q0,  q1,  [sp, #0]
    ldp q2,  q3,  [sp, #32]
    ldp q4,  q5,  [sp, #64]
    ldp q6,  q7,  [sp, #96]
    ldp q8,  q9,  [sp, #128]
    ldp q10, q11, [sp, #160]
    ldp q12, q13, [sp, #192]
    ldp q14, q15, [sp, #224]
    ldp q16, q17, [sp, #256]
    ldp q18, q19, [sp, #288]
    ldp q20, q21, [sp, #320]
    ldp q22, q23, [sp, #352]
    ldp q24, q25, [sp, #384]
    ldp q26, q27, [sp, #416]
    ldp q28, q29, [sp, #448]
    ldp q30, q31, [sp, #480]
    add sp, sp, #512

    ldp x15, x16, [sp], #16
    msr nzcv, x16
    ldp x13, x14, [sp], #16
    ldp x11, x12, [sp], #16
    ldp x9,  x10, [sp], #16
    ldp x7,  x8,  [sp], #16
    ldp x5,  x6,  [sp], #16
    ldp x3,  x4,  [sp], #16
    ldp x1,  x2,  [sp], #16
    ldp x29, x30, [sp], #16
    autibsp
    ret
.endm

SIMPLE_TRACE_TRAMP simple_trace_entry, 0
SIMPLE_TRACE_TRAMP simple_trace_exit, 1
