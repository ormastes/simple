/*
 * context.c — Thread context management for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/context/context.h"

/* ── Helpers ───────────────────────────────────────────────────────── */

static void context_zero(context_t *ctx)
{
    ctx->r0   = 0;
    ctx->r1   = 0;
    ctx->r2   = 0;
    ctx->r3   = 0;
    ctx->r4   = 0;
    ctx->r5   = 0;
    ctx->r6   = 0;
    ctx->r7   = 0;
    ctx->r8   = 0;
    ctx->r9   = 0;
    ctx->r10  = 0;
    ctx->r11  = 0;
    ctx->r12  = 0;
    ctx->sp   = 0;
    ctx->lr   = 0;
    ctx->pc   = 0;
    ctx->cpsr = 0;
}

/* ── Kernel-mode context (SVC mode) ───────────────────────────────── */

void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->pc   = entry;
    ctx->sp   = stack;
    ctx->r11  = stack;         /* Frame pointer */
    ctx->lr   = 0;             /* No return address */
    ctx->cpsr = DEFAULT_KERNEL_CPSR;
}

/* ── User-mode context (USR mode) ─────────────────────────────────── */

void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->pc   = entry;
    ctx->sp   = stack;
    ctx->r11  = stack;         /* Frame pointer */
    ctx->lr   = 0;             /* No return address */
    ctx->cpsr = DEFAULT_USER_CPSR;
}

/* ── Argument / return value ───────────────────────────────────────── */

void context_set_arg(context_t *ctx, uint32_t arg)
{
    /* ARM calling convention: first argument in r0 */
    ctx->r0 = arg;
}

uint32_t context_get_return(const context_t *ctx)
{
    /* ARM calling convention: return value in r0 */
    return ctx->r0;
}
