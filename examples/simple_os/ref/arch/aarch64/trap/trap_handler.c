/*
 * trap_handler.c — Exception dispatch for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/trap/trap_handler.h"
#include "arch/aarch64/boot/gic.h"
#include "arch/aarch64/boot/timer.h"
#include "arch/aarch64/io/uart.h"

/* ── Exception class names (for debug output) ──────────────────────── */

static const char *ec_name(uint32_t ec)
{
    switch (ec) {
    case EC_UNKNOWN:         return "Unknown";
    case EC_WFI_WFE:         return "Trapped WFI/WFE";
    case EC_SVC_AARCH64:     return "SVC (AArch64)";
    case EC_HVC_AARCH64:     return "HVC (AArch64)";
    case EC_SMC_AARCH64:     return "SMC (AArch64)";
    case EC_SYSREG:          return "System register trap";
    case EC_IABT_LOWER_EL:   return "Instruction Abort (lower EL)";
    case EC_IABT_CURRENT_EL: return "Instruction Abort (current EL)";
    case EC_PC_ALIGN:        return "PC alignment fault";
    case EC_DABT_LOWER_EL:   return "Data Abort (lower EL)";
    case EC_DABT_CURRENT_EL: return "Data Abort (current EL)";
    case EC_SP_ALIGN:        return "SP alignment fault";
    case EC_SERROR:          return "SError";
    case EC_BRK:             return "BRK (debug)";
    default:                 return "Unknown EC";
    }
}

/* ── Handler tables ────────────────────────────────────────────────── */

static irq_handler_t       irq_handlers[NUM_IRQ_HANDLERS] = { 0 };
static exception_handler_t sync_handlers[64]               = { 0 };

/* Forward declarations */
extern uint32_t syscall_dispatch(uint32_t number,
                                  uint64_t arg0, uint64_t arg1,
                                  uint64_t arg2, uint64_t arg3,
                                  uint64_t arg4);

/* ── Registration ──────────────────────────────────────────────────── */

void register_irq_handler(uint32_t irq, irq_handler_t handler)
{
    if (irq < NUM_IRQ_HANDLERS) {
        irq_handlers[irq] = handler;
    }
}

void register_sync_handler(uint32_t ec, exception_handler_t handler)
{
    if (ec < 64) {
        sync_handlers[ec] = handler;
    }
}

/* ── Default exception handler (prints info via UART) ──────────────── */

static void default_sync_handler(trap_frame_t *frame)
{
    uint32_t esr = (uint32_t)frame->esr_el1;
    uint32_t ec  = (esr >> ESR_EC_SHIFT) & 0x3F;

    uart_write("\n!!! EXCEPTION: ");
    uart_write(ec_name(ec));

    uart_write(" (EC=0x");
    uart_write_hex(ec);
    uart_write(", ESR=0x");
    uart_write_hex(esr);
    uart_write(")\n");

    uart_write("  ELR_EL1=");
    uart_write_hex(frame->elr_el1);
    uart_write("  FAR_EL1=");
    uart_write_hex(frame->far_el1);
    uart_write("\n");

    uart_write("  SPSR_EL1=");
    uart_write_hex(frame->spsr_el1);
    uart_write("  SP=");
    uart_write_hex(frame->sp);
    uart_write("\n");

    uart_write("  x0=");
    uart_write_hex(frame->x[0]);
    uart_write("  x1=");
    uart_write_hex(frame->x[1]);
    uart_write("  x2=");
    uart_write_hex(frame->x[2]);
    uart_write("  x3=");
    uart_write_hex(frame->x[3]);
    uart_write("\n");

    uart_write("  x30(LR)=");
    uart_write_hex(frame->x[30]);
    uart_write("\n");

    /* Halt on unrecoverable exceptions */
    uart_write("  SYSTEM HALTED.\n");
    while (1) {
        __asm__ volatile ("wfe");
    }
}

/* ── Handle synchronous exception ──────────────────────────────────── */

static void handle_sync(trap_frame_t *frame)
{
    uint32_t esr = (uint32_t)frame->esr_el1;
    uint32_t ec  = (esr >> ESR_EC_SHIFT) & 0x3F;

    /* Check for registered handler */
    if (sync_handlers[ec]) {
        sync_handlers[ec](frame);
        return;
    }

    /* SVC: system call */
    if (ec == EC_SVC_AARCH64) {
        uint32_t svc_num = (uint32_t)(frame->x[8]);  /* x8 = syscall number */
        uint32_t ret = syscall_dispatch(svc_num,
                                         frame->x[0], frame->x[1],
                                         frame->x[2], frame->x[3],
                                         frame->x[4]);
        frame->x[0] = ret;  /* Return value in x0 */
        return;
    }

    /* Unhandled — use default */
    default_sync_handler(frame);
}

/* ── Handle IRQ ────────────────────────────────────────────────────── */

static void handle_irq(trap_frame_t *frame)
{
    uint32_t irq = gic_acknowledge();

    if (irq == GIC_SPURIOUS_IRQ)
        return;

    /* Timer interrupt */
    if (irq == GIC_PPI_PHYS_TIMER) {
        timer_handler();
    }

    /* Check for registered device handler */
    if (irq < NUM_IRQ_HANDLERS && irq_handlers[irq]) {
        irq_handlers[irq](frame);
    }

    gic_end_interrupt(irq);
}

/* ── Main dispatch ─────────────────────────────────────────────────── */

void exception_handler(trap_frame_t *frame)
{
    uint32_t esr = (uint32_t)frame->esr_el1;
    uint32_t spsr = (uint32_t)frame->spsr_el1;

    /*
     * Determine exception type from the vector offset.
     * We can infer by examining SPSR and ESR:
     * - Check if ESR indicates sync vs IRQ
     * - For simplicity, we check the ESR EC field.
     *   If EC == 0 and the exception came from an IRQ vector,
     *   we treat it as an IRQ.
     *
     * In practice, the vector table entry determines this:
     * sync vectors call us with ESR valid,
     * IRQ vectors call us with a GIC pending interrupt.
     *
     * We use a simple heuristic: if ESR EC is non-zero or SVC,
     * it's synchronous. Otherwise check GIC for pending IRQ.
     */
    uint32_t ec = (esr >> ESR_EC_SHIFT) & 0x3F;

    if (ec != EC_UNKNOWN) {
        /* Synchronous exception with known EC */
        handle_sync(frame);
    } else {
        /*
         * EC_UNKNOWN could be a synchronous unknown or we're
         * in an IRQ vector. Try to acknowledge from GIC.
         */
        uint32_t pending = mmio_read32(GICC_BASE + GICC_IAR);
        uint32_t irq_id = pending & 0x3FF;
        if (irq_id != GIC_SPURIOUS_IRQ) {
            /* It's an IRQ */
            if (irq_id == GIC_PPI_PHYS_TIMER) {
                timer_handler();
            }
            if (irq_id < NUM_IRQ_HANDLERS && irq_handlers[irq_id]) {
                irq_handlers[irq_id](frame);
            }
            gic_end_interrupt(irq_id);
        } else {
            /* Truly unknown — log and halt */
            default_sync_handler(frame);
        }
    }
}
