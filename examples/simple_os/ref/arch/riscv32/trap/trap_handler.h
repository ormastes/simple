/*
 * trap_handler.h — Trap dispatch for RISC-V32 (M-mode)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_RISCV32_TRAP_TRAP_HANDLER_H
#define ARCH_RISCV32_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Trap frame (matches trap_entry.S push order) ────────────────────── */

typedef struct PACKED {
    /* General-purpose registers x1..x31 (x0 is always zero) */
    uint32_t ra;        /* x1  — return address         */
    uint32_t sp;        /* x2  — stack pointer          */
    uint32_t gp;        /* x3  — global pointer         */
    uint32_t tp;        /* x4  — thread pointer         */
    uint32_t t0;        /* x5  — temp 0                 */
    uint32_t t1;        /* x6  — temp 1                 */
    uint32_t t2;        /* x7  — temp 2                 */
    uint32_t s0;        /* x8  — saved / frame pointer  */
    uint32_t s1;        /* x9  — saved 1                */
    uint32_t a0;        /* x10 — arg 0 / return 0       */
    uint32_t a1;        /* x11 — arg 1 / return 1       */
    uint32_t a2;        /* x12 — arg 2                  */
    uint32_t a3;        /* x13 — arg 3                  */
    uint32_t a4;        /* x14 — arg 4                  */
    uint32_t a5;        /* x15 — arg 5                  */
    uint32_t a6;        /* x16 — arg 6                  */
    uint32_t a7;        /* x17 — arg 7                  */
    uint32_t s2;        /* x18 — saved 2                */
    uint32_t s3;        /* x19 — saved 3                */
    uint32_t s4;        /* x20 — saved 4                */
    uint32_t s5;        /* x21 — saved 5                */
    uint32_t s6;        /* x22 — saved 6                */
    uint32_t s7;        /* x23 — saved 7                */
    uint32_t s8;        /* x24 — saved 8                */
    uint32_t s9;        /* x25 — saved 9                */
    uint32_t s10;       /* x26 — saved 10               */
    uint32_t s11;       /* x27 — saved 11               */
    uint32_t t3;        /* x28 — temp 3                 */
    uint32_t t4;        /* x29 — temp 4                 */
    uint32_t t5;        /* x30 — temp 5                 */
    uint32_t t6;        /* x31 — temp 6                 */

    /* CSR state */
    uint32_t mepc;      /* Machine exception PC         */
    uint32_t mstatus;   /* Machine status               */
    uint32_t mcause;    /* Machine cause                */
    uint32_t mtval;     /* Machine trap value           */
} trap_frame_t;

/* ── mcause values ───────────────────────────────────────────────────── */

/* Interrupt bit (MSB of mcause) */
#define MCAUSE_INTERRUPT    0x80000000

/* Exception codes (mcause without interrupt bit) */
#define EXC_INST_MISALIGN   0
#define EXC_INST_FAULT      1
#define EXC_ILLEGAL_INST    2
#define EXC_BREAKPOINT      3
#define EXC_LOAD_MISALIGN   4
#define EXC_LOAD_FAULT      5
#define EXC_STORE_MISALIGN  6
#define EXC_STORE_FAULT     7
#define EXC_ECALL_U         8
#define EXC_ECALL_S         9
#define EXC_ECALL_M         11
#define EXC_INST_PAGE_FAULT 12
#define EXC_LOAD_PAGE_FAULT 13
#define EXC_STORE_PAGE_FAULT 15

/* Interrupt codes (mcause without interrupt bit) */
#define IRQ_SOFTWARE_M      3
#define IRQ_TIMER_M         7
#define IRQ_EXTERNAL_M      11

/* ── Handler function pointer types ──────────────────────────────────── */

typedef void (*exception_handler_t)(trap_frame_t *frame);
typedef void (*irq_handler_t)(trap_frame_t *frame);

/* ── Public API ──────────────────────────────────────────────────────── */

/* Called from trap_entry assembly */
void trap_handler(trap_frame_t *frame);

/* Register handlers */
void register_exception_handler(uint32_t code, exception_handler_t handler);
void register_irq_handler(uint32_t code, irq_handler_t handler);

/* System call dispatch (called internally) */
extern uint32_t syscall_dispatch(uint32_t number,
                                 uint32_t arg0, uint32_t arg1,
                                 uint32_t arg2, uint32_t arg3,
                                 uint32_t arg4);

#endif /* ARCH_RISCV32_TRAP_TRAP_HANDLER_H */
