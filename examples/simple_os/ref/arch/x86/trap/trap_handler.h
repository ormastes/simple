/*
 * trap_handler.h — Interrupt dispatch for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_TRAP_TRAP_HANDLER_H
#define ARCH_X86_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Trap frame (matches isr_common push order) ────────────────────── */

typedef struct PACKED {
    /* Pushed by isr_common */
    uint32_t ds;
    uint32_t edi, esi, ebp, _esp, ebx, edx, ecx, eax;  /* pusha order */
    uint32_t int_no;
    uint32_t err_code;

    /* Pushed by CPU on interrupt/exception */
    uint32_t eip;
    uint32_t cs;
    uint32_t eflags;
    uint32_t esp;    /* Only valid on privilege-level change */
    uint32_t ss;     /* Only valid on privilege-level change */
} trap_frame_t;

/* ── Handler function pointer type ─────────────────────────────────── */

typedef void (*exception_handler_t)(trap_frame_t *frame);
typedef void (*irq_handler_t)(trap_frame_t *frame);

/* ── Maximum counts ────────────────────────────────────────────────── */

#define NUM_EXCEPTIONS  32
#define NUM_IRQS        16
#define IRQ_BASE_VECTOR 32

/* ── Public API ────────────────────────────────────────────────────── */

/* Called from isr_common in assembly */
void trap_handler(trap_frame_t *frame);

/* Register handlers */
void register_exception_handler(uint8_t exception, exception_handler_t handler);
void register_irq_handler(uint8_t irq, irq_handler_t handler);

#endif /* ARCH_X86_TRAP_TRAP_HANDLER_H */
