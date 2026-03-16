/*
 * switch.S — 64-bit context switch assembly for x86_64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * void context_switch(context64_t *old_ctx, context64_t *new_ctx);
 *
 * System V AMD64 ABI: old = RDI, new = RSI
 *
 * We save/restore callee-saved registers (RBX, RBP, R12-R15),
 * RFLAGS, RSP, and RIP.
 */

/* Field offsets in context structure
 * (matching RegisterState64 layout) */
.set CTX_RIP,    128    /* offset of rip field */
.set CTX_RSP,    56     /* offset of rsp field */
.set CTX_RBX,    8      /* offset of rbx field */
.set CTX_RBP,    48     /* offset of rbp field */
.set CTX_R12,    96     /* offset of r12 field */
.set CTX_R13,    104    /* offset of r13 field */
.set CTX_R14,    112    /* offset of r14 field */
.set CTX_R15,    120    /* offset of r15 field */
.set CTX_RFLAGS, 136    /* offset of rflags field */

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(old, new)
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* RDI = old context, RSI = new context */

    /* Save callee-saved registers */
    movq    %rbx, CTX_RBX(%rdi)
    movq    %rbp, CTX_RBP(%rdi)
    movq    %r12, CTX_R12(%rdi)
    movq    %r13, CTX_R13(%rdi)
    movq    %r14, CTX_R14(%rdi)
    movq    %r15, CTX_R15(%rdi)

    /* Save RFLAGS */
    pushfq
    popq    CTX_RFLAGS(%rdi)

    /* Save RSP */
    movq    %rsp, CTX_RSP(%rdi)

    /* Save return address as RIP */
    movq    (%rsp), %rax
    movq    %rax, CTX_RIP(%rdi)

    /* Load new context */
    movq    CTX_RBX(%rsi), %rbx
    movq    CTX_RBP(%rsi), %rbp
    movq    CTX_R12(%rsi), %r12
    movq    CTX_R13(%rsi), %r13
    movq    CTX_R14(%rsi), %r14
    movq    CTX_R15(%rsi), %r15

    pushq   CTX_RFLAGS(%rsi)
    popfq

    movq    CTX_RSP(%rsi), %rsp

    jmp     *CTX_RIP(%rsi)

.size context_switch, . - context_switch

/* ══════════════════════════════════════════════════════════════════════
 * context_setup_stack(ctx)
 * ══════════════════════════════════════════════════════════════════════ */

.global context_setup_stack
.type   context_setup_stack, @function

context_setup_stack:
    /* RDI = context pointer */
    movq    CTX_RSP(%rdi), %rax

    /* Push fake return address */
    subq    $8, %rax
    movq    $0, (%rax)

    movq    %rax, CTX_RSP(%rdi)
    ret

.size context_setup_stack, . - context_setup_stack
