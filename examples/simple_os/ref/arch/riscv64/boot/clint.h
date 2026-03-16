/*
 * clint.h — Core Local Interruptor (CLINT) timer for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * CLINT base address: 0x02000000 on QEMU virt platform.
 *
 * The CLINT provides:
 *   - Machine Software Interrupt (msip) per hart
 *   - Machine Timer (mtimecmp / mtime) per hart
 */

#ifndef ARCH_RISCV64_BOOT_CLINT_H
#define ARCH_RISCV64_BOOT_CLINT_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── CLINT base address (QEMU virt) ───────────────────────────────── */

#define CLINT_BASE          0x02000000UL

/* ── Register offsets ─────────────────────────────────────────────── */

/* Machine Software Interrupt: 4 bytes per hart */
#define CLINT_MSIP(hart)        (CLINT_BASE + 0x0000UL + 4UL * (hart))

/* Machine Timer Compare: 8 bytes per hart */
#define CLINT_MTIMECMP(hart)    (CLINT_BASE + 0x4000UL + 8UL * (hart))

/* Machine Time: single 64-bit register (native width on RV64) */
#define CLINT_MTIME             (CLINT_BASE + 0xBFF8UL)

/* ── Timer frequency (QEMU virt default: 10 MHz) ──────────────────── */

#define CLINT_FREQ_HZ       10000000UL

/* ── MMIO helpers ─────────────────────────────────────────────────── */

static inline void clint_write32(uint64_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static inline uint32_t clint_read32(uint64_t addr)
{
    return *(volatile uint32_t *)addr;
}

static inline void clint_write64(uint64_t addr, uint64_t val)
{
    *(volatile uint64_t *)addr = val;
}

static inline uint64_t clint_read64(uint64_t addr)
{
    return *(volatile uint64_t *)addr;
}

/* ── Public API ───────────────────────────────────────────────────── */

void     clint_init(uint32_t hart_id);
uint64_t clint_get_mtime(void);
void     clint_set_mtimecmp(uint32_t hart_id, uint64_t value);
void     clint_set_timer(uint32_t hart_id, uint64_t interval);
void     clint_send_msip(uint32_t hart_id);
void     clint_clear_msip(uint32_t hart_id);

#endif /* ARCH_RISCV64_BOOT_CLINT_H */
