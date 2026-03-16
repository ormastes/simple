/*
 * trap_handler.h — Exception dispatch for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_ARM32_TRAP_TRAP_HANDLER_H
#define ARCH_ARM32_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Trap frame (matches vectors.S push order) ─────────────────────── */

typedef struct {
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
    uint32_t r11;
    uint32_t r12;
    uint32_t sp;
    uint32_t lr;
    uint32_t pc;
    uint32_t cpsr;
} trap_frame_t;

/* ── Exception types ──────────────────────────────────────────────── */

#define EXCEPTION_UNDEF         1
#define EXCEPTION_SVC           2
#define EXCEPTION_PREFETCH_ABT  3
#define EXCEPTION_DATA_ABT      4
#define EXCEPTION_IRQ           5
#define EXCEPTION_FIQ           6

/* ── ARM processor modes ──────────────────────────────────────────── */

#define MODE_USR    0x10
#define MODE_FIQ    0x11
#define MODE_IRQ    0x12
#define MODE_SVC    0x13
#define MODE_ABT    0x17
#define MODE_UND    0x1B
#define MODE_SYS    0x1F

/* ── Handler function pointer types ───────────────────────────────── */

typedef void (*irq_handler_fn)(uint32_t irq, trap_frame_t *frame);
typedef void (*exception_handler_fn)(trap_frame_t *frame);

/* ── Maximum counts ───────────────────────────────────────────────── */

#define MAX_IRQ_HANDLERS    256

/* ── Public API ────────────────────────────────────────────────────── */

/* Called from assembly vector stubs */
void handle_irq(trap_frame_t *frame);
void handle_svc(trap_frame_t *frame);
void handle_data_abort(trap_frame_t *frame);
void handle_prefetch_abort(trap_frame_t *frame);
void handle_undef(trap_frame_t *frame);
void handle_fiq(trap_frame_t *frame);

/* Register handlers */
void register_irq_handler(uint32_t irq, irq_handler_fn handler);

/* Read Data Fault Status Register (DFSR) */
uint32_t arm_read_dfsr(void);

/* Read Data Fault Address Register (DFAR) */
uint32_t arm_read_dfar(void);

/* Read Instruction Fault Status Register (IFSR) */
uint32_t arm_read_ifsr(void);

/* Read Instruction Fault Address Register (IFAR) */
uint32_t arm_read_ifar(void);

#endif /* ARCH_ARM32_TRAP_TRAP_HANDLER_H */
