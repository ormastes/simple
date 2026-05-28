/*
 * SimpleOS ARM64 minimal startup/stdout capsule.
 *
 * Policy stays in pure Simple; this file owns only PL011 MMIO writes,
 * stdout/stderr ABI hooks, module-init handoff, and the final WFE halt.
 */

#include <stdint.h>
#include <stddef.h>

#define PL011_BASE 0x09000000ULL
#define PL011_DR   0x000u
#define PL011_FR   0x018u
#define PL011_IBRD 0x024u
#define PL011_FBRD 0x028u
#define PL011_LCRH 0x02Cu
#define PL011_CR   0x030u
#define PL011_ICR  0x044u
#define PL011_TXFF (1u << 5)

static inline volatile uint32_t *pl011_reg(uint32_t offset)
{
    return (volatile uint32_t *)(PL011_BASE + offset);
}

static void pl011_init(void)
{
    *pl011_reg(PL011_CR) = 0u;
    *pl011_reg(PL011_ICR) = 0x7FFu;
    *pl011_reg(PL011_IBRD) = 1u;
    *pl011_reg(PL011_FBRD) = 0u;
    *pl011_reg(PL011_LCRH) = (3u << 5) | (1u << 4);
    *pl011_reg(PL011_CR) = (1u << 0) | (1u << 8) | (1u << 9);
}

void serial_putchar(char c)
{
    for (uint32_t spin = 0; spin < 100000u; spin++) {
        if ((*pl011_reg(PL011_FR) & PL011_TXFF) == 0u) break;
    }
    *pl011_reg(PL011_DR) = (uint32_t)(uint8_t)c;
}

#include "../../common/baremetal_min_stdout.h"

extern void spl_start(void) __attribute__((weak));
extern void __simple_call_module_inits(void) __attribute__((weak));

void _c_start(void)
{
    pl011_init();
    if (__simple_call_module_inits) __simple_call_module_inits();
    if (spl_start) spl_start();
    for (;;) {
        __asm__ volatile("wfe");
    }
}
