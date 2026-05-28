/*
 * SimpleOS ARM32 minimal startup/stdout capsule.
 *
 * Policy stays in pure Simple; this file owns only PL011 MMIO writes,
 * stdout/stderr ABI hooks, optional spl_start handoff, and WFI halt.
 */

#include <stdint.h>
#include <stddef.h>

#define PL011_BASE 0x09000000u
#define PL011_DR   (*(volatile uint32_t *)(PL011_BASE + 0x000u))
#define PL011_FR   (*(volatile uint32_t *)(PL011_BASE + 0x018u))
#define PL011_IBRD (*(volatile uint32_t *)(PL011_BASE + 0x024u))
#define PL011_FBRD (*(volatile uint32_t *)(PL011_BASE + 0x028u))
#define PL011_LCRH (*(volatile uint32_t *)(PL011_BASE + 0x02Cu))
#define PL011_CR   (*(volatile uint32_t *)(PL011_BASE + 0x030u))
#define PL011_ICR  (*(volatile uint32_t *)(PL011_BASE + 0x044u))
#define PL011_TXFF (1u << 5)

static void pl011_init(void)
{
    PL011_CR = 0u;
    PL011_ICR = 0x7FFu;
    PL011_IBRD = 13u;
    PL011_FBRD = 1u;
    PL011_LCRH = (3u << 5) | (1u << 4);
    PL011_CR = (1u << 0) | (1u << 8) | (1u << 9);
}

void serial_putchar(char c)
{
    for (uint32_t spin = 0; spin < 100000u; spin++) {
        if ((PL011_FR & PL011_TXFF) == 0u) break;
    }
    PL011_DR = (uint32_t)(uint8_t)c;
}

#include "../../common/baremetal_min_stdout.h"

extern void spl_start(void) __attribute__((weak));

void _start(void)
{
    pl011_init();
    if (spl_start) spl_start();
    for (;;) {
        __asm__ volatile("wfi");
    }
}
