/*
 * context.h — Thread context management for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Matches the Simple language RegisterState structure.
 */

#ifndef ARCH_X86_CONTEXT_CONTEXT_H
#define ARCH_X86_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Segment selectors (user-mode selectors have RPL=3) ────────────── */

#define KERNEL_CS   0x08
#define KERNEL_DS   0x10
#define USER_CS     0x1B    /* 0x18 | 3 */
#define USER_DS     0x23    /* 0x20 | 3 */

/* Default EFLAGS: IF=1 (interrupts enabled), reserved bit 1 */
#define DEFAULT_EFLAGS  0x00000202

/* ── Context structure ─────────────────────────────────────────────── */

typedef struct {
    /* Instruction pointer */
    uint32_t eip;

    /* Stack */
    uint32_t esp;

    /* Callee-saved registers */
    uint32_t ebx;
    uint32_t esi;
    uint32_t edi;
    uint32_t ebp;

    /* Flags */
    uint32_t eflags;

    /* Caller-saved registers */
    uint32_t eax;
    uint32_t ecx;
    uint32_t edx;

    /* Segment registers */
    uint32_t cs;
    uint32_t ds;
    uint32_t es;
    uint32_t fs;
    uint32_t gs;
    uint32_t ss;
} context_t;

/* ── Public API ────────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode thread */
void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack);

/* Initialise a context for a user-mode thread */
void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack);

/* Set the first argument for a new thread (placed in stack or register) */
void context_set_arg(context_t *ctx, uint32_t arg);

/* Get the return value from a context (EAX) */
uint32_t context_get_return(const context_t *ctx);

/* Defined in switch.S */
extern void context_switch(context_t *old_ctx, context_t *new_ctx);
extern void context_setup_stack(context_t *ctx);

#endif /* ARCH_X86_CONTEXT_CONTEXT_H */
