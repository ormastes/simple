/*
 * timer.c — AArch64 Generic Timer (EL1 Physical Timer)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/boot/timer.h"

/* ── State ─────────────────────────────────────────────────────────── */

static volatile uint64_t timer_tick_count = 0;
static uint32_t timer_freq_hz = 0;
static uint32_t timer_interval_ticks = 0;

/* ── System register accessors ─────────────────────────────────────── */

static inline uint64_t read_cntfrq_el0(void)
{
    uint64_t val;
    __asm__ volatile ("mrs %0, cntfrq_el0" : "=r"(val));
    return val;
}

static inline uint64_t read_cntpct_el0(void)
{
    uint64_t val;
    __asm__ volatile ("mrs %0, cntpct_el0" : "=r"(val));
    return val;
}

static inline void write_cntp_tval_el0(uint32_t val)
{
    __asm__ volatile ("msr cntp_tval_el0, %0" : : "r"((uint64_t)val));
}

static inline void write_cntp_ctl_el0(uint32_t val)
{
    __asm__ volatile ("msr cntp_ctl_el0, %0" : : "r"((uint64_t)val));
}

static inline uint32_t read_cntp_ctl_el0(void)
{
    uint64_t val;
    __asm__ volatile ("mrs %0, cntp_ctl_el0" : "=r"(val));
    return (uint32_t)val;
}

/* ── Initialisation ────────────────────────────────────────────────── */

void timer_init(void)
{
    /* Read the timer frequency */
    timer_freq_hz = (uint32_t)read_cntfrq_el0();

    /* Calculate ticks per interval */
    timer_interval_ticks = timer_freq_hz / (1000 / TIMER_INTERVAL_MS);

    /* Set the initial timer value */
    write_cntp_tval_el0(timer_interval_ticks);

    /* Enable the timer, unmask interrupt */
    write_cntp_ctl_el0(TIMER_CTL_ENABLE);

    timer_tick_count = 0;
}

/* ── Tick management ───────────────────────────────────────────────── */

uint64_t timer_get_ticks(void)
{
    return timer_tick_count;
}

uint64_t timer_get_ms(void)
{
    if (timer_freq_hz == 0)
        return 0;
    return (read_cntpct_el0() * 1000) / timer_freq_hz;
}

uint32_t timer_get_frequency(void)
{
    return timer_freq_hz;
}

/* Called from the IRQ handler when the timer PPI fires */
void timer_handler(void)
{
    timer_tick_count++;

    /* Reload the timer for the next interval */
    write_cntp_tval_el0(timer_interval_ticks);

    /* Re-enable (clear ISTATUS by writing TVAL) */
    write_cntp_ctl_el0(TIMER_CTL_ENABLE);
}

void timer_set_interval_ms(uint32_t ms)
{
    if (timer_freq_hz == 0)
        return;
    timer_interval_ticks = (timer_freq_hz * ms) / 1000;
    write_cntp_tval_el0(timer_interval_ticks);
}
