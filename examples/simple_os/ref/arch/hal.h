#ifndef SIMPLE_OS_HAL_H
#define SIMPLE_OS_HAL_H

#include "common/types.h"

/* Hardware Abstraction Layer - common interface for all architectures.
 * Each architecture provides implementations of these functions. */

void hal_serial_init(void);
void hal_serial_putc(char c);
void hal_serial_write(const char *s);

void hal_timer_init(uint32_t freq_hz);
uint64_t hal_timer_ticks(void);
uint32_t hal_timer_ms(void);

void hal_irq_enable(void);
void hal_irq_disable(void);

void hal_mmu_init(void);
void hal_mmu_map(uint32_t virt, uint32_t phys, uint32_t size, uint32_t flags);

void hal_halt(void);
void hal_panic_halt(void);

#endif
