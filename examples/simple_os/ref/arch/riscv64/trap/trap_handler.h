/*
 * trap_handler.h — Trap/interrupt dispatch for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_RISCV64_TRAP_TRAP_HANDLER_H
#define ARCH_RISCV64_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Trap frame (matches trap_entry.S push order) ─────────────────── */

typedef struct {
    /* General-purpose registers x1-x31 (x0 is hardwired zero) */
    uint64_t ra;        /* x1  */
    uint64_t sp;        /* x2  */
    uint64_t gp;        /* x3  */
    uint64_t tp;        /* x4  */
    uint64_t t0;        /* x5  */
    uint64_t t1;        /* x6  */
    uint64_t t2;        /* x7  */
    uint64_t s0;        /* x8  / fp */
    uint64_t s1;        /* x9  */
    uint64_t a0;        /* x10 */
    uint64_t a1;        /* x11 */
    uint64_t a2;        /* x12 */
    uint64_t a3;        /* x13 */
    uint64_t a4;        /* x14 */
    uint64_t a5;        /* x15 */
    uint64_t a6;        /* x16 */
    uint64_t a7;        /* x17 */
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
    uint64_t t3;        /* x28 */
    uint64_t t4;        /* x29 */
    uint64_t t5;        /* x30 */
    uint64_t t6;        /* x31 */

    /* CSRs saved by trap_entry */
    uint64_t mepc;
    uint64_t mstatus;
    uint64_t mcause;
    uint64_t mtval;
} trap_frame_t;

/* ── RISC-V exception codes ───────────────────────────────────────── */

#define EXC_INST_MISALIGNED     0
#define EXC_INST_ACCESS_FAULT   1
#define EXC_ILLEGAL_INST        2
#define EXC_BREAKPOINT          3
#define EXC_LOAD_MISALIGNED     4
#define EXC_LOAD_ACCESS_FAULT   5
#define EXC_STORE_MISALIGNED    6
#define EXC_STORE_ACCESS_FAULT  7
#define EXC_ECALL_U             8
#define EXC_ECALL_S             9
#define EXC_ECALL_M             11
#define EXC_INST_PAGE_FAULT     12
#define EXC_LOAD_PAGE_FAULT     13
#define EXC_STORE_PAGE_FAULT    15

/* ── RISC-V interrupt codes (mcause MSB set) ──────────────────────── */

#define IRQ_M_SOFTWARE          3
#define IRQ_M_TIMER             7
#define IRQ_M_EXTERNAL          11

/* ── Maximum counts ───────────────────────────────────────────────── */

#define NUM_EXCEPTIONS          16
#define NUM_IRQS                16

/* ── Handler function pointer types ───────────────────────────────── */

typedef void (*exception_handler_t)(trap_frame_t *frame);
typedef void (*irq_handler_t)(trap_frame_t *frame);

/* ── Public API ───────────────────────────────────────────────────── */

/* Called from trap_entry in assembly */
void trap_handler(trap_frame_t *frame);

/* Register handlers */
void register_exception_handler(uint8_t exception, exception_handler_t handler);
void register_irq_handler(uint8_t irq, irq_handler_t handler);

#endif /* ARCH_RISCV64_TRAP_TRAP_HANDLER_H */
