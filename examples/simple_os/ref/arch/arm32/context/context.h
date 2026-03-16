/*
 * context.h — Thread context management for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Matches the Simple language RegisterState structure.
 */

#ifndef ARCH_ARM32_CONTEXT_CONTEXT_H
#define ARCH_ARM32_CONTEXT_CONTEXT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── ARM processor modes ──────────────────────────────────────────── */

#define ARM_MODE_USR    0x10
#define ARM_MODE_FIQ    0x11
#define ARM_MODE_IRQ    0x12
#define ARM_MODE_SVC    0x13
#define ARM_MODE_ABT    0x17
#define ARM_MODE_UND    0x1B
#define ARM_MODE_SYS    0x1F

/* CPSR flag bits */
#define CPSR_I          (1 << 7)    /* IRQ disable                   */
#define CPSR_F          (1 << 6)    /* FIQ disable                   */
#define CPSR_T          (1 << 5)    /* Thumb mode                    */

/* Default CPSR for new threads: SVC mode, IRQs enabled */
#define DEFAULT_KERNEL_CPSR (ARM_MODE_SVC)
/* Default CPSR for user threads: USR mode, IRQs enabled */
#define DEFAULT_USER_CPSR   (ARM_MODE_USR)

/* ── Context structure ─────────────────────────────────────────────── */

typedef struct {
    /* General-purpose registers */
    uint32_t r0;
    uint32_t r1;
    uint32_t r2;
    uint32_t r3;
    uint32_t r4;
    uint32_t r5;
    uint32_t r6;
    uint32_t r7;
    uint32_t r8;
    uint32_t r9;
    uint32_t r10;
    uint32_t r11;  /* fp */
    uint32_t r12;  /* ip */

    /* Stack pointer */
    uint32_t sp;

    /* Link register */
    uint32_t lr;

    /* Program counter */
    uint32_t pc;

    /* Current Program Status Register */
    uint32_t cpsr;
} context_t;

/* ── Public API ────────────────────────────────────────────────────── */

/* Initialise a context for a kernel-mode thread (SVC mode) */
void context_init_kernel(context_t *ctx, uint32_t entry, uint32_t stack);

/* Initialise a context for a user-mode thread (USR mode) */
void context_init_user(context_t *ctx, uint32_t entry, uint32_t stack);

/* Set the first argument for a new thread (placed in r0) */
void context_set_arg(context_t *ctx, uint32_t arg);

/* Get the return value from a context (r0) */
uint32_t context_get_return(const context_t *ctx);

/* Defined in switch.S */
extern void context_switch(context_t *old_ctx, context_t *new_ctx);

#endif /* ARCH_ARM32_CONTEXT_CONTEXT_H */
