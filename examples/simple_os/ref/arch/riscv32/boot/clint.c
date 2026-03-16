/*
 * clint.c — CLINT (Core-Local Interruptor) timer for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/boot/clint.h"
#include "arch/riscv32/io/uart.h"

/* ── State ───────────────────────────────────────────────────────────── */

static volatile uint64_t clint_ticks = 0;
static uint32_t clint_interval = 0;

/* ── MMIO helpers ────────────────────────────────────────────────────── */

static inline void clint_write32(uint32_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static inline uint32_t clint_read32(uint32_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Initialisation ──────────────────────────────────────────────────── */

void clint_init(void)
{
    clint_ticks = 0;

    /* Default interval: 10ms (100 Hz tick rate) */
    clint_interval = CLINT_FREQ_HZ / 100;

    /* Set first timer deadline */
    uint64_t now = clint_get_time();
    clint_set_timer(now + clint_interval);

    /* Enable M-mode timer interrupt via mie CSR */
    uint32_t mie;
    __asm__ volatile ("csrr %0, mie" : "=r"(mie));
    mie |= (1 << 7);  /* MTIE — Machine Timer Interrupt Enable */
    __asm__ volatile ("csrw mie, %0" : : "r"(mie));
}

/* ── Time access ─────────────────────────────────────────────────────── */

uint64_t clint_get_time(void)
{
    /*
     * mtime is 64-bit but we're on RV32, so read in two halves.
     * Re-read high word to handle wrap-around.
     */
    uint32_t lo, hi1, hi2;
    do {
        hi1 = clint_read32(CLINT_MTIME + 4);
        lo  = clint_read32(CLINT_MTIME);
        hi2 = clint_read32(CLINT_MTIME + 4);
    } while (hi1 != hi2);

    return ((uint64_t)hi2 << 32) | lo;
}

/* ── Timer compare ───────────────────────────────────────────────────── */

void clint_set_timer(uint64_t when)
{
    /*
     * Write high word as max first to prevent spurious interrupt,
     * then low word, then correct high word.
     */
    uint32_t addr = CLINT_MTIMECMP(0);
    clint_write32(addr + 4, 0xFFFFFFFF);
    clint_write32(addr,     (uint32_t)(when & 0xFFFFFFFF));
    clint_write32(addr + 4, (uint32_t)(when >> 32));
}

void clint_set_timer_ms(uint32_t ms)
{
    uint64_t now = clint_get_time();
    uint64_t delta = (uint64_t)ms * (CLINT_FREQ_HZ / 1000);
    clint_set_timer(now + delta);
}

/* ── Timer interrupt handler ─────────────────────────────────────────── */

void clint_handler(void)
{
    clint_ticks++;

    /* Schedule next timer interrupt */
    uint64_t now = clint_get_time();
    clint_set_timer(now + clint_interval);
}

/* ── Software interrupt (IPI) ────────────────────────────────────────── */

void clint_send_ipi(uint32_t hart)
{
    clint_write32(CLINT_MSIP(hart), 1);
}

void clint_clear_ipi(uint32_t hart)
{
    clint_write32(CLINT_MSIP(hart), 0);
}
