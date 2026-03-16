/*
 * switch.S — Context switch assembly for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * void context_switch(context_t *old_ctx, context_t *new_ctx);
 *
 * context_t layout (offsets in bytes):
 *    0: eip
 *    4: esp
 *    8: ebx
 *   12: esi
 *   16: edi
 *   20: ebp
 *   24: eflags
 *   28: eax
 *   32: ecx
 *   36: edx
 *   40: cs
 *   44: ds
 *   48: es
 *   52: fs
 *   56: gs
 *   60: ss
 */

/* Field offsets in context_t */
.set CTX_EIP,    0
.set CTX_ESP,    4
.set CTX_EBX,    8
.set CTX_ESI,   12
.set CTX_EDI,   16
.set CTX_EBP,   20
.set CTX_EFLAGS,24
.set CTX_EAX,   28
.set CTX_ECX,   32
.set CTX_EDX,   36
.set CTX_CS,    40
.set CTX_DS,    44
.set CTX_ES,    48
.set CTX_FS,    52
.set CTX_GS,    56
.set CTX_SS,    60

/* ══════════════════════════════════════════════════════════════════════
 * context_switch(context_t *old, context_t *new)
 *
 * Save callee-saved registers + EFLAGS + ESP into *old,
 * then load them from *new and jump to new->eip.
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global context_switch
.type   context_switch, @function

context_switch:
    /* Arguments: old = 4(%esp), new = 8(%esp) */
    movl    4(%esp), %eax           /* eax = old context pointer */
    movl    8(%esp), %edx           /* edx = new context pointer */

    /* ── Save current state into old context ── */

    /* Save callee-saved registers */
    movl    %ebx, CTX_EBX(%eax)
    movl    %esi, CTX_ESI(%eax)
    movl    %edi, CTX_EDI(%eax)
    movl    %ebp, CTX_EBP(%eax)

    /* Save EFLAGS */
    pushfl
    popl    CTX_EFLAGS(%eax)

    /* Save ESP (after pushfl/popl, ESP is back to original) */
    movl    %esp, CTX_ESP(%eax)

    /* Save return address as EIP (the address after 'call context_switch') */
    movl    (%esp), %ecx            /* return address on stack */
    movl    %ecx, CTX_EIP(%eax)

    /* ── Load state from new context ── */

    /* Load callee-saved registers */
    movl    CTX_EBX(%edx), %ebx
    movl    CTX_ESI(%edx), %esi
    movl    CTX_EDI(%edx), %edi
    movl    CTX_EBP(%edx), %ebp

    /* Load EFLAGS */
    pushl   CTX_EFLAGS(%edx)
    popfl

    /* Load stack pointer */
    movl    CTX_ESP(%edx), %esp

    /* Jump to the new context's EIP */
    jmp     *CTX_EIP(%edx)

.size context_switch, . - context_switch

/* ══════════════════════════════════════════════════════════════════════
 * context_setup_stack(context_t *ctx)
 *
 * Build an initial stack frame for a new thread so that when
 * context_switch restores it, execution begins at ctx->eip.
 *
 * The stack is set up so the thread entry point is "returned to"
 * by the switch logic.
 * ══════════════════════════════════════════════════════════════════════ */

.global context_setup_stack
.type   context_setup_stack, @function

context_setup_stack:
    movl    4(%esp), %eax           /* eax = context pointer */

    /* Get the stack top from the context */
    movl    CTX_ESP(%eax), %ecx

    /*
     * Push a fake return address (0 = no caller) and the entry point
     * so that when context_switch does 'jmp *CTX_EIP', it goes to
     * our thread_entry_trampoline below. The trampoline then calls
     * the real entry via the saved eip.
     */

    /* Reserve space for the return address on the thread's stack */
    subl    $4, %ecx
    movl    $0, (%ecx)              /* No return address (thread_exit) */

    /* Update the context's ESP to point to this prepared stack */
    movl    %ecx, CTX_ESP(%eax)

    ret

.size context_setup_stack, . - context_setup_stack
