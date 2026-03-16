/*
 * hal.c — HAL implementation for ARM32
 *
 * Thin wrappers mapping the generic HAL interface to ARM32-specific drivers.
 * Uses PL011 UART, ARMv7 generic timer, and CP15 for IRQ/MMU control.
 */

#include "arch/hal.h"
#include "arch/arm32/io/uart.h"
#include "arch/arm32/boot/timer.h"
#include "arch/arm32/mm/paging.h"

void hal_serial_init(void)                { uart_init(); }
void hal_serial_putc(char c)              { uart_putc(c); }
void hal_serial_write(const char *s)      { uart_write(s); }

void hal_timer_init(uint32_t freq_hz)     { timer_init(freq_hz); }
uint64_t hal_timer_ticks(void)            { return timer_get_ticks(); }
uint32_t hal_timer_ms(void)               { return (uint32_t)timer_get_ms(); }

void hal_irq_enable(void)                 { __asm__ volatile("cpsie i"); }
void hal_irq_disable(void)               { __asm__ volatile("cpsid i"); }

void hal_mmu_init(void)                   { paging_init(); }
void hal_mmu_map(uint32_t virt, uint32_t phys, uint32_t size, uint32_t flags)
{
    paging_map(virt, phys, flags);
    (void)size;
}

void hal_halt(void)                       { __asm__ volatile("wfi"); }
void hal_panic_halt(void)                 { __asm__ volatile("cpsid i"); for(;;) __asm__ volatile("wfi"); }
