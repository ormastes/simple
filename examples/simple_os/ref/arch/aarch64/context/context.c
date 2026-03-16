/*
 * context.c — Thread context management for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/context/context.h"

/* ── Helpers ───────────────────────────────────────────────────────── */

static void context_zero(context_t *ctx)
{
    for (int i = 0; i < 31; i++)
        ctx->x[i] = 0;

    ctx->sp       = 0;
    ctx->elr_el1  = 0;
    ctx->spsr_el1 = 0;
}

/* ── Kernel-mode context ───────────────────────────────────────────── */

void context_init_kernel(context_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->elr_el1  = entry;
    ctx->sp       = stack;
    ctx->spsr_el1 = DEFAULT_KERNEL_SPSR;

    /* x29 (FP) = stack top for initial frame */
    ctx->x[29] = stack;
}

/* ── User-mode context ─────────────────────────────────────────────── */

void context_init_user(context_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->elr_el1  = entry;
    ctx->sp       = stack;
    ctx->spsr_el1 = DEFAULT_USER_SPSR;

    ctx->x[29] = stack;
}

/* ── Argument / return value ───────────────────────────────────────── */

void context_set_arg(context_t *ctx, uint64_t arg)
{
    /* AArch64 ABI: first argument in x0 */
    ctx->x[0] = arg;
}

uint64_t context_get_return(const context_t *ctx)
{
    /* AArch64 ABI: return value in x0 */
    return ctx->x[0];
}
