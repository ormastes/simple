/*
 * pic.c — 8259 Programmable Interrupt Controller for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Identical to the x86 version — the PIC hardware interface is unchanged.
 */

#include "arch/x86_64/boot/pic.h"

/* Small I/O delay for PIC timing requirements */
static inline void io_wait(void)
{
    outb(0x80, 0);  /* Port 0x80 is used for POST codes — safe delay */
}

/* ── Initialisation (remap IRQs to vectors 32..47) ─────────────────── */

void pic_init(void)
{
    /* Save current masks */
    uint8_t mask1 = inb(PIC1_DATA);
    uint8_t mask2 = inb(PIC2_DATA);

    /* ICW1: begin initialisation sequence */
    outb(PIC1_COMMAND, ICW1_INIT | ICW1_ICW4);
    io_wait();
    outb(PIC2_COMMAND, ICW1_INIT | ICW1_ICW4);
    io_wait();

    /* ICW2: vector offsets */
    outb(PIC1_DATA, PIC1_OFFSET);       /* IRQ 0..7  -> 32..39  */
    io_wait();
    outb(PIC2_DATA, PIC2_OFFSET);       /* IRQ 8..15 -> 40..47  */
    io_wait();

    /* ICW3: cascade wiring */
    outb(PIC1_DATA, 0x04);  /* Slave on IRQ2 (bit 2) */
    io_wait();
    outb(PIC2_DATA, 0x02);  /* Slave identity = 2     */
    io_wait();

    /* ICW4: 8086 mode */
    outb(PIC1_DATA, ICW4_8086);
    io_wait();
    outb(PIC2_DATA, ICW4_8086);
    io_wait();

    /* Restore saved masks */
    outb(PIC1_DATA, mask1);
    outb(PIC2_DATA, mask2);
}

/* ── End of Interrupt ──────────────────────────────────────────────── */

void pic_send_eoi(uint8_t irq)
{
    if (irq >= 8) {
        outb(PIC2_COMMAND, PIC_EOI);
    }
    outb(PIC1_COMMAND, PIC_EOI);
}

/* ── IRQ masking ───────────────────────────────────────────────────── */

void pic_mask_irq(uint8_t irq)
{
    uint16_t port;
    uint8_t  line = irq;

    if (irq < 8) {
        port = PIC1_DATA;
    } else {
        port = PIC2_DATA;
        line -= 8;
    }

    uint8_t val = inb(port) | (uint8_t)(1 << line);
    outb(port, val);
}

void pic_unmask_irq(uint8_t irq)
{
    uint16_t port;
    uint8_t  line = irq;

    if (irq < 8) {
        port = PIC1_DATA;
    } else {
        port = PIC2_DATA;
        line -= 8;
    }

    uint8_t val = inb(port) & (uint8_t)~(1 << line);
    outb(port, val);
}

/* ── Status register queries ───────────────────────────────────────── */

uint16_t pic_get_isr(void)
{
    outb(PIC1_COMMAND, PIC_READ_ISR);
    outb(PIC2_COMMAND, PIC_READ_ISR);
    return (uint16_t)((inb(PIC2_COMMAND) << 8) | inb(PIC1_COMMAND));
}

uint16_t pic_get_irr(void)
{
    outb(PIC1_COMMAND, PIC_READ_IRR);
    outb(PIC2_COMMAND, PIC_READ_IRR);
    return (uint16_t)((inb(PIC2_COMMAND) << 8) | inb(PIC1_COMMAND));
}

/* ── Spurious IRQ detection ────────────────────────────────────────── */

bool pic_is_spurious(uint8_t irq)
{
    uint16_t isr = pic_get_isr();

    if (irq == 7) {
        /* Spurious IRQ7: check ISR bit 7 of master */
        return (isr & (1 << 7)) == 0;
    }
    if (irq == 15) {
        /* Spurious IRQ15: check ISR bit 15 of slave */
        if ((isr & (1 << 15)) == 0) {
            /* Still need to send EOI to master (cascade line) */
            outb(PIC1_COMMAND, PIC_EOI);
            return true;
        }
    }
    return false;
}
