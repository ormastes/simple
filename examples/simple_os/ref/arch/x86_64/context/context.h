/*
 * context.h — 64-bit thread context management for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_64_CONTEXT_CONTEXT_H
#define ARCH_X86_64_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Segment selectors (user-mode selectors have RPL=3) ────────────── */

#define KERNEL_CS64 0x08
#define KERNEL_DS64 0x10
#define USER_CS64   0x1B    /* 0x18 | 3 */
#define USER_DS64   0x23    /* 0x20 | 3 */

/* Default RFLAGS: IF=1 (interrupts enabled), reserved bit 1 */
#define DEFAULT_RFLAGS  0x0000000000000202ULL

/* ── Context structure ─────────────────────────────────────────────── */

typedef struct {
    /* Instruction pointer */
    uint64_t rip;

    /* Stack pointer */
    uint64_t rsp;

    /* Callee-saved registers (System V AMD64 ABI) */
    uint64_t rbx;
    uint64_t rbp;
    uint64_t r12;
    uint64_t r13;
    uint64_t r14;
    uint64_t r15;

    /* Flags */
    uint64_t rflags;

    /* Caller-saved / argument registers */
    uint64_t rax;
    uint64_t rcx;
    uint64_t rdx;
    uint64_t rsi;
    uint64_t rdi;
    uint64_t r8;
    uint64_t r9;
    uint64_t r10;
    uint64_t r11;

    /* Segment selectors */
    uint64_t cs;
    uint64_t ds;
    uint64_t ss;

    /* FS/GS base (for TLS and per-CPU data) */
    uint64_t fs_base;
    uint64_t gs_base;
} context64_t;

/* ── Public API ────────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode thread */
void context_init_kernel(context64_t *ctx, uint64_t entry, uint64_t stack);

/* Initialise a context for a user-mode thread */
void context_init_user(context64_t *ctx, uint64_t entry, uint64_t stack);

/* Set the first argument for a new thread (RDI in System V ABI) */
void context_set_arg(context64_t *ctx, uint64_t arg);

/* Get the return value from a context (RAX) */
uint64_t context_get_return(const context64_t *ctx);

/* Defined in switch.S */
extern void context_switch(context64_t *old_ctx, context64_t *new_ctx);
extern void context_setup_stack(context64_t *ctx);

#endif /* ARCH_X86_64_CONTEXT_CONTEXT_H */
