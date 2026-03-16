/*
 * context.h — Thread context management for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Matches the Simple language RegisterState structure.
 */

#ifndef ARCH_AARCH64_CONTEXT_CONTEXT_H
#define ARCH_AARCH64_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── SPSR_EL1 mode values ──────────────────────────────────────────── */

#define SPSR_EL1H       0x05    /* EL1h: kernel mode, SP_EL1          */
#define SPSR_EL0T       0x00    /* EL0t: user mode, SP_EL0            */

/* DAIF mask bits in SPSR */
#define SPSR_D          (1 << 9)    /* Debug mask                     */
#define SPSR_A          (1 << 8)    /* SError mask                    */
#define SPSR_I          (1 << 7)    /* IRQ mask                       */
#define SPSR_F          (1 << 6)    /* FIQ mask                       */
#define SPSR_DAIF_ALL   (SPSR_D | SPSR_A | SPSR_I | SPSR_F)

/* Default kernel SPSR: EL1h, interrupts enabled (DAIF cleared) */
#define DEFAULT_KERNEL_SPSR     SPSR_EL1H

/* Default user SPSR: EL0t, interrupts enabled (DAIF cleared) */
#define DEFAULT_USER_SPSR       SPSR_EL0T

/* ── Context structure ─────────────────────────────────────────────── */

typedef struct {
    /* General-purpose registers x0-x30 */
    uint64_t x[31];

    /* Stack pointer */
    uint64_t sp;

    /* Exception return state */
    uint64_t elr_el1;       /* Return address                       */
    uint64_t spsr_el1;      /* Saved program status                 */
} context_t;

/* ── Public API ────────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode thread */
void context_init_kernel(context_t *ctx, uint64_t entry, uint64_t stack);

/* Initialise a context for a user-mode thread */
void context_init_user(context_t *ctx, uint64_t entry, uint64_t stack);

/* Set the first argument for a new thread (x0) */
void context_set_arg(context_t *ctx, uint64_t arg);

/* Get the return value from a context (x0) */
uint64_t context_get_return(const context_t *ctx);

/* Defined in switch.S */
extern void context_switch(context_t *old_ctx, context_t *new_ctx);

#endif /* ARCH_AARCH64_CONTEXT_CONTEXT_H */
