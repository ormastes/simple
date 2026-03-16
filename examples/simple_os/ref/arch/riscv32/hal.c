/*
 * hal.c — HAL implementation for RISC-V 32-bit
 *
 * Thin wrappers mapping the generic HAL interface to RISC-V32-specific drivers.
 * Uses 16550 UART, CLINT timer, and CSR instructions for IRQ control.
 */

#include "arch/hal.h"
#include "arch/riscv32/io/uart.h"
#include "arch/riscv32/boot/clint.h"
#include "arch/riscv32/mm/paging.h"

void hal_serial_init(void)                { uart_init(); }
void hal_serial_putc(char c)              { uart_putc(c); }
void hal_serial_write(const char *s)      { uart_write(s); }

void hal_timer_init(uint32_t freq_hz)     { clint_init(); (void)freq_hz; }
uint64_t hal_timer_ticks(void)            { return clint_get_time(); }
uint32_t hal_timer_ms(void)               { return (uint32_t)(clint_get_time() / (CLINT_FREQ_HZ / 1000)); }

void hal_irq_enable(void)                 { __asm__ volatile("csrsi mstatus, 0x8"); }
void hal_irq_disable(void)               { __asm__ volatile("csrci mstatus, 0x8"); }

void hal_mmu_init(void)                   { paging_init(); }
void hal_mmu_map(uint32_t virt, uint32_t phys, uint32_t size, uint32_t flags)
{
    paging_map(virt, phys, flags);
    (void)size;
}

void hal_halt(void)                       { __asm__ volatile("wfi"); }
void hal_panic_halt(void)                 { __asm__ volatile("csrci mstatus, 0x8"); for(;;) __asm__ volatile("wfi"); }
