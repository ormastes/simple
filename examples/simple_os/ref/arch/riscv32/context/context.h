/*
 * context.h — Thread context management for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Matches the Simple language RegisterState structure.
 */

#ifndef ARCH_RISCV32_CONTEXT_CONTEXT_H
#define ARCH_RISCV32_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── mstatus bits ────────────────────────────────────────────────────── */

#define MSTATUS_MIE     (1 << 3)    /* Machine Interrupt Enable         */
#define MSTATUS_MPIE    (1 << 7)    /* Machine Previous IE              */
#define MSTATUS_MPP_M   (3 << 11)   /* Machine Previous Privilege: M    */
#define MSTATUS_MPP_S   (1 << 11)   /* Machine Previous Privilege: S    */
#define MSTATUS_MPP_U   (0 << 11)   /* Machine Previous Privilege: U    */

/* Default mstatus for new threads: MPIE set (interrupts enabled on mret) */
#define DEFAULT_MSTATUS_KERNEL  (MSTATUS_MPIE | MSTATUS_MPP_M)
#define DEFAULT_MSTATUS_USER    (MSTATUS_MPIE | MSTATUS_MPP_U)

/* ── Context structure ───────────────────────────────────────────────── */

typedef struct {
    /* Return address (also serves as entry point for new threads) */
    uint32_t ra;        /* x1  */

    /* Stack pointer */
    uint32_t sp;        /* x2  */

    /* Callee-saved registers */
    uint32_t s0;        /* x8  — frame pointer  */
    uint32_t s1;        /* x9  */
    uint32_t s2;        /* x18 */
    uint32_t s3;        /* x19 */
    uint32_t s4;        /* x20 */
    uint32_t s5;        /* x21 */
    uint32_t s6;        /* x22 */
    uint32_t s7;        /* x23 */
    uint32_t s8;        /* x24 */
    uint32_t s9;        /* x25 */
    uint32_t s10;       /* x26 */
    uint32_t s11;       /* x27 */

    /* Argument/return registers (for passing data to new threads) */
    uint32_t a0;        /* x10 */
    uint32_t a1;        /* x11 */

    /* CSR state for privilege transitions */
    uint32_t mepc;      /* Machine exception PC         */
    uint32_t mstatus;   /* Machine status               */
} context_t;

/* ── Public API ──────────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode (M-mode) thread */
void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack);

/* Initialise a context for a user-mode (U-mode) thread */
void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack);

/* Set the first argument for a new thread (in a0) */
void context_set_arg(context_t *ctx, uint32_t arg);

/* Get the return value from a context (a0) */
uint32_t context_get_return(const context_t *ctx);

/* Defined in switch.S */
extern void context_switch(context_t *old_ctx, context_t *new_ctx);

#endif /* ARCH_RISCV32_CONTEXT_CONTEXT_H */
