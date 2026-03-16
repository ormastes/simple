/*
 * pit.c — 8253/8254 Programmable Interval Timer for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Identical to the x86 version — the PIT hardware interface is unchanged.
 */

#include "arch/x86_64/boot/pit.h"
#include "arch/x86_64/io/uart.h"  /* outb / inb */

/* ── State ─────────────────────────────────────────────────────────── */

static volatile uint64_t pit_ticks = 0;
static uint32_t pit_freq = 0;

/* ── Initialisation ────────────────────────────────────────────────── */

void pit_init(uint32_t freq_hz)
{
    pit_freq = freq_hz;

    uint16_t divisor = (uint16_t)(PIT_BASE_FREQ / freq_hz);

    /*
     * Command byte:
     *   Bits 7-6: Channel 0    (00)
     *   Bits 5-4: lo/hi byte   (11)
     *   Bits 3-1: Mode 2 (rate generator) (010)
     *   Bit 0:    Binary mode  (0)
     *   = 0x34
     */
    outb(PIT_COMMAND, 0x34);

    /* Send divisor (low byte first, then high byte) */
    outb(PIT_CHANNEL0, (uint8_t)(divisor & 0xFF));
    outb(PIT_CHANNEL0, (uint8_t)((divisor >> 8) & 0xFF));
}

/* ── Tick management ───────────────────────────────────────────────── */

uint64_t pit_get_ticks(void)
{
    return pit_ticks;
}

uint64_t pit_get_ms(void)
{
    if (pit_freq == 0)
        return 0;
    return (pit_ticks * 1000) / pit_freq;
}

/* Called from IRQ0 handler */
void pit_handler(void)
{
    pit_ticks++;
}
