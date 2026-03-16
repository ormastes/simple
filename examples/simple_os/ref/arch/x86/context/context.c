/*
 * context.c — Thread context management for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86/context/context.h"

/* ── Helpers ───────────────────────────────────────────────────────── */

static void context_zero(context_t *ctx)
{
    ctx->eip    = 0;
    ctx->esp    = 0;
    ctx->ebx    = 0;
    ctx->esi    = 0;
    ctx->edi    = 0;
    ctx->ebp    = 0;
    ctx->eflags = 0;
    ctx->eax    = 0;
    ctx->ecx    = 0;
    ctx->edx    = 0;
    ctx->cs     = 0;
    ctx->ds     = 0;
    ctx->es     = 0;
    ctx->fs     = 0;
    ctx->gs     = 0;
    ctx->ss     = 0;
}

/* ── Kernel-mode context ───────────────────────────────────────────── */

void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->eip    = entry;
    ctx->esp    = stack;
    ctx->eflags = DEFAULT_EFLAGS;

    /* Kernel segments */
    ctx->cs = KERNEL_CS;
    ctx->ds = KERNEL_DS;
    ctx->es = KERNEL_DS;
    ctx->fs = KERNEL_DS;
    ctx->gs = KERNEL_DS;
    ctx->ss = KERNEL_DS;
}

/* ── User-mode context ─────────────────────────────────────────────── */

void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->eip    = entry;
    ctx->esp    = stack;
    ctx->eflags = DEFAULT_EFLAGS;

    /* User segments (RPL=3) */
    ctx->cs = USER_CS;
    ctx->ds = USER_DS;
    ctx->es = USER_DS;
    ctx->fs = USER_DS;
    ctx->gs = USER_DS;
    ctx->ss = USER_DS;
}

/* ── Argument / return value ───────────────────────────────────────── */

void context_set_arg(context_t *ctx, uint32_t arg)
{
    /*
     * For cdecl on x86-32, the first argument is on the stack.
     * We push it below the current ESP so the thread entry sees
     * it as the first parameter.
     */
    ctx->esp -= 4;
    *((uint32_t *)ctx->esp) = arg;
}

uint32_t context_get_return(const context_t *ctx)
{
    return ctx->eax;
}
