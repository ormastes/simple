/*
 * trap_handler.c — 64-bit interrupt dispatch for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/x86_64/trap/trap_handler.h"
#include "arch/x86_64/boot/pic.h"
#include "arch/x86_64/io/uart.h"

/* ── Exception name strings ────────────────────────────────────────── */

static const char *exception_names[NUM_EXCEPTIONS] = {
    "Divide Error",                 /*  0 */
    "Debug",                        /*  1 */
    "Non-Maskable Interrupt",       /*  2 */
    "Breakpoint",                   /*  3 */
    "Overflow",                     /*  4 */
    "Bound Range Exceeded",         /*  5 */
    "Invalid Opcode",               /*  6 */
    "Device Not Available",         /*  7 */
    "Double Fault",                 /*  8 */
    "Coprocessor Segment Overrun",  /*  9 */
    "Invalid TSS",                  /* 10 */
    "Segment Not Present",          /* 11 */
    "Stack-Segment Fault",          /* 12 */
    "General Protection Fault",     /* 13 */
    "Page Fault",                   /* 14 */
    "Reserved",                     /* 15 */
    "x87 FPU Error",                /* 16 */
    "Alignment Check",              /* 17 */
    "Machine Check",                /* 18 */
    "SIMD Floating-Point",          /* 19 */
    "Virtualisation Exception",     /* 20 */
    "Control Protection",           /* 21 */
    "Reserved",                     /* 22 */
    "Reserved",                     /* 23 */
    "Reserved",                     /* 24 */
    "Reserved",                     /* 25 */
    "Reserved",                     /* 26 */
    "Reserved",                     /* 27 */
    "Reserved",                     /* 28 */
    "Security Exception",           /* 29 */
    "Hypervisor Injection",         /* 30 */
    "Reserved",                     /* 31 */
};

/* ── Handler tables ────────────────────────────────────────────────── */

static exception_handler64_t exception_handlers[NUM_EXCEPTIONS] = { 0 };
static irq_handler64_t       irq_handlers[NUM_IRQS]             = { 0 };

/* ── Registration ──────────────────────────────────────────────────── */

void register_exception_handler(uint8_t exception, exception_handler64_t handler)
{
    if (exception < NUM_EXCEPTIONS) {
        exception_handlers[exception] = handler;
    }
}

void register_irq_handler(uint8_t irq, irq_handler64_t handler)
{
    if (irq < NUM_IRQS) {
        irq_handlers[irq] = handler;
    }
}

/* ── Default exception handler (prints info via UART) ──────────────── */

static void default_exception_handler(trap_frame64_t *frame)
{
    uart_write("\n!!! EXCEPTION: ");
    if (frame->int_no < NUM_EXCEPTIONS) {
        uart_write(exception_names[frame->int_no]);
    } else {
        uart_write("Unknown");
    }

    uart_write(" (vector ");
    uart_write_dec((uint32_t)frame->int_no);
    uart_write(", error=");
    uart_write_hex64(frame->err_code);
    uart_write(")\n");

    uart_write("  RIP=");
    uart_write_hex64(frame->rip);
    uart_write("  CS=");
    uart_write_hex((uint32_t)frame->cs);
    uart_write("  RFLAGS=");
    uart_write_hex64(frame->rflags);
    uart_write("\n");

    uart_write("  RAX=");
    uart_write_hex64(frame->rax);
    uart_write("  RBX=");
    uart_write_hex64(frame->rbx);
    uart_write("  RCX=");
    uart_write_hex64(frame->rcx);
    uart_write("  RDX=");
    uart_write_hex64(frame->rdx);
    uart_write("\n");

    uart_write("  RSP=");
    uart_write_hex64(frame->rsp);
    uart_write("  RBP=");
    uart_write_hex64(frame->rbp);
    uart_write("  RSI=");
    uart_write_hex64(frame->rsi);
    uart_write("  RDI=");
    uart_write_hex64(frame->rdi);
    uart_write("\n");

    uart_write("  R8=");
    uart_write_hex64(frame->r8);
    uart_write("  R9=");
    uart_write_hex64(frame->r9);
    uart_write("  R10=");
    uart_write_hex64(frame->r10);
    uart_write("  R11=");
    uart_write_hex64(frame->r11);
    uart_write("\n");

    uart_write("  R12=");
    uart_write_hex64(frame->r12);
    uart_write("  R13=");
    uart_write_hex64(frame->r13);
    uart_write("  R14=");
    uart_write_hex64(frame->r14);
    uart_write("  R15=");
    uart_write_hex64(frame->r15);
    uart_write("\n");

    /* Halt on unrecoverable exceptions */
    uart_write("  SYSTEM HALTED.\n");
    __asm__ volatile ("cli; hlt");
}

/* ── Main dispatch ─────────────────────────────────────────────────── */

void trap_handler(trap_frame64_t *frame)
{
    uint64_t int_no = frame->int_no;

    if (int_no < NUM_EXCEPTIONS) {
        /* CPU exception */
        if (exception_handlers[int_no]) {
            exception_handlers[int_no](frame);
        } else {
            default_exception_handler(frame);
        }
    } else if (int_no >= IRQ_BASE_VECTOR &&
               int_no < IRQ_BASE_VECTOR + NUM_IRQS) {
        /* Hardware IRQ */
        uint8_t irq = (uint8_t)(int_no - IRQ_BASE_VECTOR);

        /* Check for spurious IRQs */
        if (pic_is_spurious(irq))
            return;

        if (irq_handlers[irq]) {
            irq_handlers[irq](frame);
        }

        pic_send_eoi(irq);
    } else {
        /* Unknown vector — log and ignore */
        uart_write("Unknown interrupt vector: ");
        uart_write_dec((uint32_t)int_no);
        uart_write("\n");
    }
}
