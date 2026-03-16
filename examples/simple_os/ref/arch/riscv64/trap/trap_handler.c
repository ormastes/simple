/*
 * trap_handler.c — Trap/interrupt dispatch for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/trap/trap_handler.h"
#include "arch/riscv64/boot/plic.h"
#include "arch/riscv64/boot/clint.h"
#include "arch/riscv64/io/uart.h"

/* ── Exception name strings ───────────────────────────────────────── */

static const char *exception_names[NUM_EXCEPTIONS] = {
    "Instruction address misaligned",   /*  0 */
    "Instruction access fault",         /*  1 */
    "Illegal instruction",              /*  2 */
    "Breakpoint",                       /*  3 */
    "Load address misaligned",          /*  4 */
    "Load access fault",                /*  5 */
    "Store/AMO address misaligned",     /*  6 */
    "Store/AMO access fault",           /*  7 */
    "Environment call from U-mode",     /*  8 */
    "Environment call from S-mode",     /*  9 */
    "Reserved",                         /* 10 */
    "Environment call from M-mode",     /* 11 */
    "Instruction page fault",           /* 12 */
    "Load page fault",                  /* 13 */
    "Reserved",                         /* 14 */
    "Store/AMO page fault",             /* 15 */
};

/* ── Handler tables ───────────────────────────────────────────────── */

static exception_handler_t exception_handlers[NUM_EXCEPTIONS] = { 0 };
static irq_handler_t       irq_handlers[NUM_IRQS]             = { 0 };

/* ── Registration ─────────────────────────────────────────────────── */

void register_exception_handler(uint8_t exception, exception_handler_t handler)
{
    if (exception < NUM_EXCEPTIONS) {
        exception_handlers[exception] = handler;
    }
}

void register_irq_handler(uint8_t irq, irq_handler_t handler)
{
    if (irq < NUM_IRQS) {
        irq_handlers[irq] = handler;
    }
}

/* ── Default exception handler (prints info via UART) ─────────────── */

static void default_exception_handler(trap_frame_t *frame)
{
    uart_write("\n!!! EXCEPTION: ");
    uint64_t code = frame->mcause & 0x7FFFFFFFFFFFFFFFUL;
    if (code < NUM_EXCEPTIONS) {
        uart_write(exception_names[code]);
    } else {
        uart_write("Unknown");
    }

    uart_write(" (cause ");
    uart_write_hex(frame->mcause);
    uart_write(", mtval=");
    uart_write_hex(frame->mtval);
    uart_write(")\n");

    uart_write("  MEPC=");
    uart_write_hex(frame->mepc);
    uart_write("  RA=");
    uart_write_hex(frame->ra);
    uart_write("  SP=");
    uart_write_hex(frame->sp);
    uart_write("\n");

    uart_write("  A0=");
    uart_write_hex(frame->a0);
    uart_write("  A1=");
    uart_write_hex(frame->a1);
    uart_write("  A7=");
    uart_write_hex(frame->a7);
    uart_write("\n");

    /* Halt on unrecoverable exceptions */
    uart_write("  SYSTEM HALTED.\n");
    while (1) {
        __asm__ volatile ("wfi");
    }
}

/* ── Main dispatch ────────────────────────────────────────────────── */

void trap_handler(trap_frame_t *frame)
{
    uint64_t mcause = frame->mcause;

    if (mcause & (1UL << 63)) {
        /* Interrupt (MSB set) */
        uint64_t irq_code = mcause & 0x7FFFFFFFFFFFFFFFUL;

        if (irq_code < NUM_IRQS && irq_handlers[irq_code]) {
            irq_handlers[irq_code](frame);
        } else if (irq_code == IRQ_M_TIMER) {
            /* Default timer handling: schedule next tick */
            uint64_t now = clint_get_mtime();
            clint_set_mtimecmp(0, now + CLINT_FREQ_HZ / 100);
        } else if (irq_code == IRQ_M_EXTERNAL) {
            /* External interrupt via PLIC */
            uint32_t src = plic_claim(PLIC_CONTEXT_M0);
            if (src > 0) {
                /* Handle and complete */
                plic_complete(PLIC_CONTEXT_M0, src);
            }
        }
    } else {
        /* Exception (synchronous trap) */
        uint64_t code = mcause;
        if (code < NUM_EXCEPTIONS && exception_handlers[code]) {
            exception_handlers[code](frame);
        } else {
            default_exception_handler(frame);
        }
    }
}
