/*
 * context.c — Thread context management for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/context/context.h"

/* ── Helpers ─────────────────────────────────────────────────────────── */

static void context_zero(context_t *ctx)
{
    ctx->ra      = 0;
    ctx->sp      = 0;
    ctx->s0      = 0;
    ctx->s1      = 0;
    ctx->s2      = 0;
    ctx->s3      = 0;
    ctx->s4      = 0;
    ctx->s5      = 0;
    ctx->s6      = 0;
    ctx->s7      = 0;
    ctx->s8      = 0;
    ctx->s9      = 0;
    ctx->s10     = 0;
    ctx->s11     = 0;
    ctx->a0      = 0;
    ctx->a1      = 0;
    ctx->mepc    = 0;
    ctx->mstatus = 0;
}

/* ── Kernel-mode context (M-mode) ────────────────────────────────────── */

void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->ra      = entry;
    ctx->sp      = stack;
    ctx->s0      = stack;       /* Frame pointer = stack top */
    ctx->mepc    = entry;
    ctx->mstatus = DEFAULT_MSTATUS_KERNEL;
}

/* ── User-mode context (U-mode: mstatus.MPP = 0) ────────────────────── */

void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack)
{
    context_zero(ctx);

    ctx->ra      = entry;
    ctx->sp      = stack;
    ctx->s0      = stack;       /* Frame pointer = stack top */
    ctx->mepc    = entry;
    ctx->mstatus = DEFAULT_MSTATUS_USER;
}

/* ── Argument / return value ─────────────────────────────────────────── */

void context_set_arg(context_t *ctx, uint32_t arg)
{
    ctx->a0 = arg;
}

uint32_t context_get_return(const context_t *ctx)
{
    return ctx->a0;
}
