/*
 * pit.h — 8253/8254 Programmable Interval Timer for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_BOOT_PIT_H
#define ARCH_X86_BOOT_PIT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PIT port addresses ────────────────────────────────────────────── */

#define PIT_CHANNEL0    0x40
#define PIT_CHANNEL1    0x41
#define PIT_CHANNEL2    0x42
#define PIT_COMMAND     0x43

/* ── PIT base frequency ────────────────────────────────────────────── */

#define PIT_BASE_FREQ   1193182  /* Hz */

/* ── Public API ────────────────────────────────────────────────────── */

void     pit_init(uint32_t freq_hz);
uint64_t pit_get_ticks(void);
uint64_t pit_get_ms(void);
void     pit_handler(void);

#endif /* ARCH_X86_BOOT_PIT_H */
