/*
 * context.c — 64-bit thread context management for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/context/context.h"

/* ── Helpers ───────────────────────────────────────────────────────── */

static void context_zero(context64_t *ctx)
{
    ctx->rip    = 0;
    ctx->rsp    = 0;
    ctx->rbx    = 0;
    ctx->rbp    = 0;
    ctx->r12    = 0;
    ctx->r13    = 0;
    ctx->r14    = 0;
    ctx->r15    = 0;
    ctx->rflags = 0;
    ctx->rax    = 0;
    ctx->rcx    = 0;
    ctx->rdx    = 0;
    ctx->rsi    = 0;
    ctx->rdi    = 0;
    ctx->r8     = 0;
    ctx->r9     = 0;
    ctx->r10    = 0;
    ctx->r11    = 0;
    ctx->cs     = 0;
    ctx->ds     = 0;
    ctx->ss     = 0;
    ctx->fs_base = 0;
    ctx->gs_base = 0;
}

/* ── Kernel-mode context ───────────────────────────────────────────── */

void context_init_kernel(context64_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->rip    = entry;
    ctx->rsp    = stack;
    ctx->rflags = DEFAULT_RFLAGS;

    /* Kernel segments */
    ctx->cs = KERNEL_CS64;
    ctx->ds = KERNEL_DS64;
    ctx->ss = KERNEL_DS64;
}

/* ── User-mode context ─────────────────────────────────────────────── */

void context_init_user(context64_t *ctx, uint64_t entry, uint64_t stack)
{
    context_zero(ctx);

    ctx->rip    = entry;
    ctx->rsp    = stack;
    ctx->rflags = DEFAULT_RFLAGS;

    /* User segments (RPL=3) */
    ctx->cs = USER_CS64;
    ctx->ds = USER_DS64;
    ctx->ss = USER_DS64;
}

/* ── Argument / return value ───────────────────────────────────────── */

void context_set_arg(context64_t *ctx, uint64_t arg)
{
    /* System V AMD64 ABI: first argument in RDI */
    ctx->rdi = arg;
}

uint64_t context_get_return(const context64_t *ctx)
{
    return ctx->rax;
}
