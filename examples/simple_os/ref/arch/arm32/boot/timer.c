/*
 * timer.c — ARMv7 Generic Timer for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Uses MRC/MCR to access the ARMv7 generic timer via CP15.
 */

#include "arch/arm32/boot/timer.h"
#include "arch/arm32/boot/gic.h"

/* ── State ─────────────────────────────────────────────────────────── */

static volatile uint64_t timer_ticks = 0;
static uint32_t timer_freq = 0;       /* CNTFRQ value               */
static uint32_t timer_interval = 0;   /* Reload value per tick      */

/* ── CP15 Generic Timer access ────────────────────────────────────── */

/* Read CNTFRQ (Counter Frequency) */
static inline uint32_t read_cntfrq(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c14, c0, 0" : "=r"(val));
    return val;
}

/* Read CNTPCT (Physical Count — 64-bit) */
static inline uint64_t read_cntpct(void)
{
    uint32_t lo, hi;
    __asm__ volatile ("mrrc p15, 0, %0, %1, c14" : "=r"(lo), "=r"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/* Write CNTP_TVAL (Physical Timer Value) */
static inline void write_cntp_tval(uint32_t val)
{
    __asm__ volatile ("mcr p15, 0, %0, c14, c2, 0" : : "r"(val));
}

/* Read CNTP_TVAL */
static inline uint32_t read_cntp_tval(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c14, c2, 0" : "=r"(val));
    return val;
}

/* Write CNTP_CTL (Physical Timer Control) */
static inline void write_cntp_ctl(uint32_t val)
{
    __asm__ volatile ("mcr p15, 0, %0, c14, c2, 1" : : "r"(val));
}

/* Read CNTP_CTL */
static inline uint32_t read_cntp_ctl(void)
{
    uint32_t val;
    __asm__ volatile ("mrc p15, 0, %0, c14, c2, 1" : "=r"(val));
    return val;
}

/* ── Initialisation ────────────────────────────────────────────────── */

void timer_init(uint32_t freq_hz)
{
    /* Read the hardware counter frequency */
    timer_freq = read_cntfrq();

    /* Calculate interval: ticks per desired interrupt frequency */
    if (freq_hz == 0)
        freq_hz = TICK_FREQ_HZ;
    timer_interval = timer_freq / freq_hz;

    timer_ticks = 0;

    /* Set the timer value */
    write_cntp_tval(timer_interval);

    /* Enable the timer, unmask interrupts */
    write_cntp_ctl(CNTP_CTL_ENABLE);

    /* Enable the timer IRQ in the GIC */
    gic_enable_irq(TIMER_PPI_IRQ);
    gic_set_priority(TIMER_PPI_IRQ, 0x00);
}

/* ── Tick management ───────────────────────────────────────────────── */

uint64_t timer_get_ticks(void)
{
    return timer_ticks;
}

uint64_t timer_get_ms(void)
{
    if (timer_freq == 0)
        return 0;
    return (read_cntpct() * 1000) / timer_freq;
}

uint32_t timer_get_frequency(void)
{
    return timer_freq;
}

void timer_set_interval(uint32_t ticks)
{
    timer_interval = ticks;
    write_cntp_tval(ticks);
}

/* ── IRQ handler (called from trap dispatch) ──────────────────────── */

void timer_handler(void)
{
    timer_ticks++;

    /* Reload the timer for the next period */
    write_cntp_tval(timer_interval);
}
