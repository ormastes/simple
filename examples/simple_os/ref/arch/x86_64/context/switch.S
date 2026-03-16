/*
 * switch.S — 64-bit context switch assembly for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context64_t *old_ctx, context64_t *new_ctx);
 *
 * context64_t layout (offsets in bytes):
 *    0: rip
 *    8: rsp
 *   16: rbx
 *   24: rbp
 *   32: r12
 *   40: r13
 *   48: r14
 *   56: r15
 *   64: rflags
 *   72: rax
 *   ...
 */

/* Field offsets in context64_t */
.set CTX_RIP,    0
.set CTX_RSP,    8
.set CTX_RBX,   16
.set CTX_RBP,   24
.set CTX_R12,   32
.set CTX_R13,   40
.set CTX_R14,   48
.set CTX_R15,   56
.set CTX_RFLAGS,64

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context64_t *old, context64_t *new)
 *
 * System V AMD64 ABI: old = RDI, new = RSI
 *
 * Save callee-saved registers + RFLAGS + RSP into *old,
 * then load them from *new and jump to new->rip.
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* RDI = old context pointer, RSI = new context pointer */

    /* ── Save current state into old context ── */

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
    movq    (%rsp), %rax            /* return address on stack */
    movq    %rax, CTX_RIP(%rdi)

    /* ── Load state from new context ── */

    /* Load callee-saved registers */
    movq    CTX_RBX(%rsi), %rbx
    movq    CTX_RBP(%rsi), %rbp
    movq    CTX_R12(%rsi), %r12
    movq    CTX_R13(%rsi), %r13
    movq    CTX_R14(%rsi), %r14
    movq    CTX_R15(%rsi), %r15

    /* Load RFLAGS */
    pushq   CTX_RFLAGS(%rsi)
    popfq

    /* Load stack pointer */
    movq    CTX_RSP(%rsi), %rsp

    /* Jump to the new context's RIP */
    jmp     *CTX_RIP(%rsi)

.size context_switch, . - context_switch

/* ══════════════════════════════════════════════════════════════════════
 * context_setup_stack(context64_t *ctx)
 *
 * Build an initial stack frame for a new thread so that when
 * context_switch restores it, execution begins at ctx->rip.
 * ══════════════════════════════════════════════════════════════════════ */

.global context_setup_stack
.type   context_setup_stack, @function

context_setup_stack:
    /* RDI = context pointer */

    /* Get the stack top from the context */
    movq    CTX_RSP(%rdi), %rax

    /* Push a fake return address (0 = no caller) */
    subq    $8, %rax
    movq    $0, (%rax)

    /* Update the context's RSP */
    movq    %rax, CTX_RSP(%rdi)

    ret

.size context_setup_stack, . - context_setup_stack
