/*
 * trap_handler.c — Exception dispatch for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/trap/trap_handler.h"
#include "arch/arm32/boot/gic.h"
#include "arch/arm32/boot/timer.h"
#include "arch/arm32/io/uart.h"

/* ── Handler table ─────────────────────────────────────────────────── */

static irq_handler_fn irq_handlers[MAX_IRQ_HANDLERS] = { 0 };

/* ── Handler registration ──────────────────────────────────────────── */

void register_irq_handler(uint32_t irq, irq_handler_fn handler)
{
    if (irq < MAX_IRQ_HANDLERS) {
        irq_handlers[irq] = handler;
    }
}

/* ── Fault status register access via CP15 ─────────────────────────── */

uint32_t arm_read_dfsr(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c5, c0, 0" : "=r"(val));
    return val;
}

uint32_t arm_read_dfar(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c6, c0, 0" : "=r"(val));
    return val;
}

uint32_t arm_read_ifsr(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c5, c0, 1" : "=r"(val));
    return val;
}

uint32_t arm_read_ifar(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c6, c0, 2" : "=r"(val));
    return val;
}

/* ── IRQ handler ───────────────────────────────────────────────────── */

void handle_irq(trap_frame_t *frame)
{
    uint32_t irq = gic_acknowledge();

    if (irq == GIC_SPURIOUS_IRQ)
        return;

    /* Timer IRQ */
    if (irq == TIMER_PPI_IRQ) {
        timer_handler();
    }

    /* Dispatch to registered handler */
    if (irq < MAX_IRQ_HANDLERS && irq_handlers[irq]) {
        irq_handlers[irq](irq, frame);
    }

    gic_end_interrupt(irq);
}

/* ── SVC handler (syscall) ─────────────────────────────────────────── */

void handle_svc(trap_frame_t *frame)
{
    /*
     * Extract SVC number from the SVC instruction.
     * The SVC instruction encodes the number in the lower 24 bits.
     * The faulting instruction is at frame->pc (LR was already adjusted).
     *
     * For the L4-style syscall convention:
     *   r7 = syscall number
     *   r0-r5 = arguments
     *   return value in r0
     */
    uint32_t syscall_num = frame->r7;

    /* TODO: dispatch to syscall handler */
    uart_write("SVC #");
    uart_write_dec(syscall_num);
    uart_write("\n");

    /* Return value goes in r0 */
    frame->r0 = 0;
}

/* ── Data Abort handler ────────────────────────────────────────────── */

void handle_data_abort(trap_frame_t *frame)
{
    uint32_t dfsr = arm_read_dfsr();
    uint32_t dfar = arm_read_dfar();

    uart_write("\n!!! DATA ABORT\n");
    uart_write("  DFAR=");
    uart_write_hex(dfar);
    uart_write("  DFSR=");
    uart_write_hex(dfsr);
    uart_write("\n");

    uart_write("  PC=");
    uart_write_hex(frame->pc);
    uart_write("  LR=");
    uart_write_hex(frame->lr);
    uart_write("  SP=");
    uart_write_hex(frame->sp);
    uart_write("\n");

    uart_write("  r0=");
    uart_write_hex(frame->r0);
    uart_write("  r1=");
    uart_write_hex(frame->r1);
    uart_write("  r2=");
    uart_write_hex(frame->r2);
    uart_write("  r3=");
    uart_write_hex(frame->r3);
    uart_write("\n");

    uart_write("  CPSR=");
    uart_write_hex(frame->cpsr);
    uart_write("\n");

    uart_write("  SYSTEM HALTED.\n");

    /* Halt */
    __asm__ volatile ("cpsid if");
    for (;;)
        __asm__ volatile ("wfi");
}

/* ── Prefetch Abort handler ────────────────────────────────────────── */

void handle_prefetch_abort(trap_frame_t *frame)
{
    uint32_t ifsr = arm_read_ifsr();
    uint32_t ifar = arm_read_ifar();

    uart_write("\n!!! PREFETCH ABORT\n");
    uart_write("  IFAR=");
    uart_write_hex(ifar);
    uart_write("  IFSR=");
    uart_write_hex(ifsr);
    uart_write("\n");

    uart_write("  PC=");
    uart_write_hex(frame->pc);
    uart_write("  LR=");
    uart_write_hex(frame->lr);
    uart_write("\n");

    uart_write("  SYSTEM HALTED.\n");

    __asm__ volatile ("cpsid if");
    for (;;)
        __asm__ volatile ("wfi");
}

/* ── Undefined Instruction handler ─────────────────────────────────── */

void handle_undef(trap_frame_t *frame)
{
    uart_write("\n!!! UNDEFINED INSTRUCTION\n");
    uart_write("  PC=");
    uart_write_hex(frame->pc);
    uart_write("  LR=");
    uart_write_hex(frame->lr);
    uart_write("\n");

    uart_write("  SYSTEM HALTED.\n");

    __asm__ volatile ("cpsid if");
    for (;;)
        __asm__ volatile ("wfi");
}

/* ── FIQ handler ───────────────────────────────────────────────────── */

void handle_fiq(trap_frame_t *frame)
{
    (void)frame;
    /* FIQ is not used in this implementation */
    uart_write("FIQ received (unexpected)\n");
}
