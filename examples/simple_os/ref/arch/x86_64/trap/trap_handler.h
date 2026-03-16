/*
 * trap_handler.h — 64-bit interrupt dispatch for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_64_TRAP_TRAP_HANDLER_H
#define ARCH_X86_64_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── 64-bit trap frame (matches isr_common push order) ─────────────── */

typedef struct PACKED {
    /* Pushed by isr_common (in reverse order of push) */
    uint64_t r15, r14, r13, r12, r11, r10, r9, r8;
    uint64_t rbp;
    uint64_t rdi, rsi;
    uint64_t rdx, rcx, rbx, rax;

    /* Pushed by ISR stub */
    uint64_t int_no;
    uint64_t err_code;

    /* Pushed by CPU on interrupt/exception */
    uint64_t rip;
    uint64_t cs;
    uint64_t rflags;
    uint64_t rsp;       /* Always present in long mode */
    uint64_t ss;        /* Always present in long mode */
} trap_frame64_t;

/* ── Handler function pointer types ────────────────────────────────── */

typedef void (*exception_handler64_t)(trap_frame64_t *frame);
typedef void (*irq_handler64_t)(trap_frame64_t *frame);

/* ── Maximum counts ────────────────────────────────────────────────── */

#define NUM_EXCEPTIONS  32
#define NUM_IRQS        16
#define IRQ_BASE_VECTOR 32

/* ── Public API ────────────────────────────────────────────────────── */

/* Called from isr_common in assembly */
void trap_handler(trap_frame64_t *frame);

/* Register handlers */
void register_exception_handler(uint8_t exception, exception_handler64_t handler);
void register_irq_handler(uint8_t irq, irq_handler64_t handler);

#endif /* ARCH_X86_64_TRAP_TRAP_HANDLER_H */
