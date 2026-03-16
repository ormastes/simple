/*
 * context.c — Thread context management for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/context/context.h"

/* ── Helpers ──────────────────────────────────────────────────────── */

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
    ctx->a2      = 0;
    ctx->a3      = 0;
    ctx->a4      = 0;
    ctx->a5      = 0;
    ctx->a6      = 0;
    ctx->a7      = 0;
    ctx->tp      = 0;
    ctx->gp      = 0;
    ctx->mstatus = 0;
    ctx->mepc    = 0;
}

/* ── Kernel-mode context (M-mode: mstatus.MPP=3) ──────────────────── */

void context_init_kernel(context_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->ra     = entry;
    ctx->sp     = stack;
    ctx->s0     = stack;       /* frame pointer = stack top */
    ctx->mepc   = entry;
    ctx->mstatus = MSTATUS_MPIE | MPP_M;
}

/* ── User-mode context (U-mode: mstatus.MPP=0) ────────────────────── */

void context_init_user(context_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->ra     = entry;
    ctx->sp     = stack;
    ctx->s0     = stack;       /* frame pointer = stack top */
    ctx->mepc   = entry;
    ctx->mstatus = MSTATUS_MPIE | MPP_U;
}

/* ── Argument / return value ──────────────────────────────────────── */

void context_set_arg(context_t *ctx, uint64_t arg)
{
    ctx->a0 = arg;
}

uint64_t context_get_return(const context_t *ctx)
{
    return ctx->a0;
}
