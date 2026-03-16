/*
 * clint.c — Core Local Interruptor (CLINT) timer for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/boot/clint.h"

/* ── State ────────────────────────────────────────────────────────── */

static volatile uint64_t timer_ticks = 0;
static uint64_t timer_interval = 0;

/* ── Initialisation ───────────────────────────────────────────────── */

void clint_init(uint32_t hart_id)
{
    timer_ticks = 0;

    /* Set timer to fire in 10ms (100 Hz tick rate) */
    timer_interval = CLINT_FREQ_HZ / 100;

    uint64_t now = clint_get_mtime();
    clint_set_mtimecmp(hart_id, now + timer_interval);

    /* Enable machine timer interrupt in mie CSR */
    uint64_t mie;
    __asm__ volatile ("csrr %0, mie" : "=r"(mie));
    mie |= (1UL << 7);  /* MTIE bit */
    __asm__ volatile ("csrw mie, %0" : : "r"(mie));
}

/* ── Timer read ───────────────────────────────────────────────────── */

uint64_t clint_get_mtime(void)
{
    return clint_read64(CLINT_MTIME);
}

/* ── Timer compare ────────────────────────────────────────────────── */

void clint_set_mtimecmp(uint32_t hart_id, uint64_t value)
{
    /* On RV64, we can do a single 64-bit write */
    clint_write64(CLINT_MTIMECMP(hart_id), value);
}

void clint_set_timer(uint32_t hart_id, uint64_t interval)
{
    timer_interval = interval;
    uint64_t now = clint_get_mtime();
    clint_set_mtimecmp(hart_id, now + interval);
}

/* ── Software interrupt ───────────────────────────────────────────── */

void clint_send_msip(uint32_t hart_id)
{
    clint_write32(CLINT_MSIP(hart_id), 1);
}

void clint_clear_msip(uint32_t hart_id)
{
    clint_write32(CLINT_MSIP(hart_id), 0);
}
