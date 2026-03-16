/*
 * clint.h — CLINT (Core-Local Interruptor) timer for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * QEMU virt CLINT base: 0x02000000
 *
 * CLINT memory map:
 *   0x02000000 + hart*4   : msip (software interrupt pending)
 *   0x02004000 + hart*8   : mtimecmp (64-bit timer compare)
 *   0x0200BFF8            : mtime (64-bit free-running timer)
 */

#ifndef ARCH_RISCV32_BOOT_CLINT_H
#define ARCH_RISCV32_BOOT_CLINT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── CLINT base address (QEMU virt) ──────────────────────────────────── */

#define CLINT_BASE          0x02000000

/* ── CLINT register addresses ────────────────────────────────────────── */

#define CLINT_MSIP(hart)        (CLINT_BASE + 0x0000 + (hart) * 4)
#define CLINT_MTIMECMP(hart)    (CLINT_BASE + 0x4000 + (hart) * 8)
#define CLINT_MTIME             (CLINT_BASE + 0xBFF8)

/* Timer frequency: QEMU virt uses 10 MHz */
#define CLINT_FREQ_HZ       10000000

/* ── Public API ──────────────────────────────────────────────────────── */

void     clint_init(void);
uint64_t clint_get_time(void);
void     clint_set_timer(uint64_t when);
void     clint_set_timer_ms(uint32_t ms);
void     clint_handler(void);

/* Software interrupt (IPI) */
void     clint_send_ipi(uint32_t hart);
void     clint_clear_ipi(uint32_t hart);

#endif /* ARCH_RISCV32_BOOT_CLINT_H */
