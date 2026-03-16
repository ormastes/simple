/*
 * hal.c — HAL implementation for x86
 *
 * Thin wrappers mapping the generic HAL interface to x86-specific drivers.
 */

#include "arch/hal.h"
#include "arch/x86/io/uart.h"
#include "arch/x86/boot/pit.h"
#include "arch/x86/mm/paging.h"

void hal_serial_init(void)                { uart_init(); }
void hal_serial_putc(char c)              { uart_putc(c); }
void hal_serial_write(const char *s)      { uart_write(s); }

void hal_timer_init(uint32_t freq_hz)     { pit_init(freq_hz); }
uint64_t hal_timer_ticks(void)            { return pit_get_ticks(); }
uint32_t hal_timer_ms(void)               { return pit_get_ms(); }

void hal_irq_enable(void)                 { __asm__ volatile("sti"); }
void hal_irq_disable(void)               { __asm__ volatile("cli"); }

void hal_mmu_init(void)                   { paging_init(); }
void hal_mmu_map(uint32_t virt, uint32_t phys, uint32_t size, uint32_t flags)
{
    paging_map(virt, phys, flags);
    (void)size;
}

void hal_halt(void)                       { __asm__ volatile("hlt"); }
void hal_panic_halt(void)                 { __asm__ volatile("cli"); for(;;) __asm__ volatile("hlt"); }
