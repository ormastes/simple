/*
 * timer.h — ARMv7 Generic Timer for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Uses the physical timer (CNTP) accessible via CP15.
 */

#ifndef ARCH_ARM32_BOOT_TIMER_H
#define ARCH_ARM32_BOOT_TIMER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Generic Timer IRQ (PPI 14 = GIC IRQ 30 on QEMU virt) ────────── */

#define TIMER_PPI_IRQ       30

/* ── CNTP_CTL bits ────────────────────────────────────────────────── */

#define CNTP_CTL_ENABLE     (1 << 0)    /* Timer enable              */
#define CNTP_CTL_IMASK      (1 << 1)    /* Interrupt mask            */
#define CNTP_CTL_ISTATUS    (1 << 2)    /* Timer condition met       */

/* ── Public API ────────────────────────────────────────────────────── */

void     timer_init(uint32_t freq_hz);
uint64_t timer_get_ticks(void);
uint64_t timer_get_ms(void);
void     timer_handler(void);
uint32_t timer_get_frequency(void);
void     timer_set_interval(uint32_t ticks);

#endif /* ARCH_ARM32_BOOT_TIMER_H */
