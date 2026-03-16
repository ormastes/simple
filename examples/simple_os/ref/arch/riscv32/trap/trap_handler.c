/*
 * trap_handler.c — Trap dispatch for RISC-V32 (M-mode)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/trap/trap_handler.h"
#include "arch/riscv32/boot/plic.h"
#include "arch/riscv32/boot/clint.h"
#include "arch/riscv32/io/uart.h"

/* ── Exception name strings ──────────────────────────────────────────── */

#define NUM_EXCEPTIONS  16

static const char *exception_names[NUM_EXCEPTIONS] = {
    "Instruction Address Misaligned",   /*  0 */
    "Instruction Access Fault",         /*  1 */
    "Illegal Instruction",              /*  2 */
    "Breakpoint",                       /*  3 */
    "Load Address Misaligned",          /*  4 */
    "Load Access Fault",                /*  5 */
    "Store Address Misaligned",         /*  6 */
    "Store Access Fault",               /*  7 */
    "Environment Call from U-mode",     /*  8 */
    "Environment Call from S-mode",     /*  9 */
    "Reserved",                         /* 10 */
    "Environment Call from M-mode",     /* 11 */
    "Instruction Page Fault",           /* 12 */
    "Load Page Fault",                  /* 13 */
    "Reserved",                         /* 14 */
    "Store Page Fault",                 /* 15 */
};

/* ── Handler tables ──────────────────────────────────────────────────── */

#define NUM_IRQ_CODES   16

static exception_handler_t exception_handlers[NUM_EXCEPTIONS] = { 0 };
static irq_handler_t       irq_handlers[NUM_IRQ_CODES]        = { 0 };

/* ── Registration ────────────────────────────────────────────────────── */

void register_exception_handler(uint32_t code, exception_handler_t handler)
{
    if (code < NUM_EXCEPTIONS) {
        exception_handlers[code] = handler;
    }
}

void register_irq_handler(uint32_t code, irq_handler_t handler)
{
    if (code < NUM_IRQ_CODES) {
        irq_handlers[code] = handler;
    }
}

/* ── Default exception handler (prints info via UART and halts) ──────── */

static void default_exception_handler(trap_frame_t *frame)
{
    uint32_t cause = frame->mcause & ~MCAUSE_INTERRUPT;

    uart_write("\n!!! EXCEPTION: ");
    if (cause < NUM_EXCEPTIONS) {
        uart_write(exception_names[cause]);
    } else {
        uart_write("Unknown");
    }

    uart_write(" (cause ");
    uart_write_dec(cause);
    uart_write(")\n");

    uart_write("  mepc=");
    uart_write_hex(frame->mepc);
    uart_write("  mtval=");
    uart_write_hex(frame->mtval);
    uart_write("  mstatus=");
    uart_write_hex(frame->mstatus);
    uart_write("\n");

    uart_write("  ra=");
    uart_write_hex(frame->ra);
    uart_write("  sp=");
    uart_write_hex(frame->sp);
    uart_write("  gp=");
    uart_write_hex(frame->gp);
    uart_write("\n");

    uart_write("  a0=");
    uart_write_hex(frame->a0);
    uart_write("  a1=");
    uart_write_hex(frame->a1);
    uart_write("  a7=");
    uart_write_hex(frame->a7);
    uart_write("\n");

    uart_write("  SYSTEM HALTED.\n");

    /* Halt: disable interrupts and loop in wfi */
    __asm__ volatile (
        "csrc mstatus, %0\n"
        "1: wfi\n"
        "   j 1b\n"
        : : "r"(1 << 3)
    );
}

/* ── Ecall (system call) handler ─────────────────────────────────────── */

static void handle_ecall(trap_frame_t *frame)
{
    /* a7 = syscall number, a0-a5 = arguments */
    uint32_t result = syscall_dispatch(
        frame->a7,
        frame->a0, frame->a1, frame->a2,
        frame->a3, frame->a4
    );

    /* Return value in a0 */
    frame->a0 = result;

    /* Advance past the ecall instruction (4 bytes) */
    frame->mepc += 4;
}

/* ── Main dispatch ───────────────────────────────────────────────────── */

void trap_handler(trap_frame_t *frame)
{
    uint32_t mcause = frame->mcause;

    if (mcause & MCAUSE_INTERRUPT) {
        /* ── Interrupt ── */
        uint32_t code = mcause & ~MCAUSE_INTERRUPT;

        switch (code) {
        case IRQ_TIMER_M:
            /* Machine timer interrupt */
            clint_handler();
            if (irq_handlers[IRQ_TIMER_M]) {
                irq_handlers[IRQ_TIMER_M](frame);
            }
            break;

        case IRQ_EXTERNAL_M:
            /* Machine external interrupt — service via PLIC */
            {
                uint32_t irq = plic_claim(PLIC_CONTEXT_M0);
                if (irq != 0) {
                    if (irq_handlers[IRQ_EXTERNAL_M]) {
                        irq_handlers[IRQ_EXTERNAL_M](frame);
                    }
                    plic_complete(PLIC_CONTEXT_M0, irq);
                }
            }
            break;

        case IRQ_SOFTWARE_M:
            /* Machine software interrupt (IPI) */
            clint_clear_ipi(0);
            if (irq_handlers[IRQ_SOFTWARE_M]) {
                irq_handlers[IRQ_SOFTWARE_M](frame);
            }
            break;

        default:
            uart_write("Unknown interrupt code: ");
            uart_write_dec(code);
            uart_write("\n");
            break;
        }
    } else {
        /* ── Exception ── */
        uint32_t code = mcause;

        if (code == EXC_ECALL_U || code == EXC_ECALL_S || code == EXC_ECALL_M) {
            handle_ecall(frame);
        } else if (code < NUM_EXCEPTIONS && exception_handlers[code]) {
            exception_handlers[code](frame);
        } else {
            default_exception_handler(frame);
        }
    }
}
