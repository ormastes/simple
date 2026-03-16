/*
 * timer.h — AArch64 Generic Timer (EL1 Physical Timer)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * Uses system registers: CNTFRQ_EL0, CNTP_TVAL_EL0, CNTP_CTL_EL0,
 * CNTPCT_EL0.
 */

#ifndef ARCH_AARCH64_BOOT_TIMER_H
#define ARCH_AARCH64_BOOT_TIMER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── CNTP_CTL_EL0 bits ────────────────────────────────────────────── */

#define TIMER_CTL_ENABLE    (1 << 0)    /* Timer enable               */
#define TIMER_CTL_IMASK     (1 << 1)    /* Interrupt mask (1=masked)  */
#define TIMER_CTL_ISTATUS   (1 << 2)    /* Timer condition met        */

/* ── Default timer interval ───────────────────────────────────────── */

#define TIMER_INTERVAL_MS   10          /* 10 ms tick period          */

/* ── Public API ────────────────────────────────────────────────────── */

void     timer_init(void);
uint64_t timer_get_ticks(void);
uint64_t timer_get_ms(void);
uint32_t timer_get_frequency(void);
void     timer_handler(void);
void     timer_set_interval_ms(uint32_t ms);

#endif /* ARCH_AARCH64_BOOT_TIMER_H */
