/*
 * context.h — Thread context management for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Matches the Simple language RegisterState structure.
 */

#ifndef ARCH_RISCV64_CONTEXT_CONTEXT_H
#define ARCH_RISCV64_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── mstatus.MPP field values ─────────────────────────────────────── */

#define MPP_U       (0UL << 11)     /* User mode       */
#define MPP_S       (1UL << 11)     /* Supervisor mode  */
#define MPP_M       (3UL << 11)     /* Machine mode     */
#define MPP_MASK    (3UL << 11)

/* Default mstatus: MPIE=1 (interrupts enabled on mret), MPP per mode */
#define MSTATUS_MPIE    (1UL << 7)

/* ── Context structure ────────────────────────────────────────────── */

typedef struct {
    /* Return address / instruction pointer */
    uint64_t ra;        /* x1  */

    /* Stack pointer */
    uint64_t sp;        /* x2  */

    /* Callee-saved registers */
    uint64_t s0;        /* x8  / fp */
    uint64_t s1;        /* x9  */
    uint64_t s2;        /* x18 */
    uint64_t s3;        /* x19 */
    uint64_t s4;        /* x20 */
    uint64_t s5;        /* x21 */
    uint64_t s6;        /* x22 */
    uint64_t s7;        /* x23 */
    uint64_t s8;        /* x24 */
    uint64_t s9;        /* x25 */
    uint64_t s10;       /* x26 */
    uint64_t s11;       /* x27 */

    /* Argument / return registers */
    uint64_t a0;        /* x10 */
    uint64_t a1;        /* x11 */
    uint64_t a2;        /* x12 */
    uint64_t a3;        /* x13 */
    uint64_t a4;        /* x14 */
    uint64_t a5;        /* x15 */
    uint64_t a6;        /* x16 */
    uint64_t a7;        /* x17 */

    /* Thread pointer / global pointer */
    uint64_t tp;        /* x4  */
    uint64_t gp;        /* x3  */

    /* Status register (mstatus) */
    uint64_t mstatus;

    /* Program counter (mepc) */
    uint64_t mepc;
} context_t;

/* ── Public API ───────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode (M-mode) thread */
void context_init_kernel(context_t *ctx, uint64_t entry, uint64_t stack);

/* Initialise a context for a user-mode (U-mode) thread */
void context_init_user(context_t *ctx, uint64_t entry, uint64_t stack);

/* Set the first argument for a new thread (a0 register) */
void context_set_arg(context_t *ctx, uint64_t arg);

/* Get the return value from a context (a0) */
uint64_t context_get_return(const context_t *ctx);

/* Defined in switch.S */
extern void context_switch(context_t *old_ctx, context_t *new_ctx);

#endif /* ARCH_RISCV64_CONTEXT_CONTEXT_H */
