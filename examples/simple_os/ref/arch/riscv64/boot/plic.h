/*
 * plic.h — Platform-Level Interrupt Controller for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * PLIC base address: 0x0C000000 on QEMU virt platform.
 */

#ifndef ARCH_RISCV64_BOOT_PLIC_H
#define ARCH_RISCV64_BOOT_PLIC_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PLIC base address (QEMU virt) ────────────────────────────────── */

#define PLIC_BASE               0x0C000000UL

/* ── PLIC register regions ────────────────────────────────────────── */

/* Source priority: offset 0x000000 + 4*source_id */
#define PLIC_PRIORITY(src)      (PLIC_BASE + 0x000000UL + 4UL * (src))

/* Pending bits: offset 0x001000 + 4*(source_id/32) */
#define PLIC_PENDING(src)       (PLIC_BASE + 0x001000UL + 4UL * ((src) / 32))

/* Enable bits per hart/context: offset 0x002000 + 0x80*context + 4*(source_id/32) */
#define PLIC_ENABLE(ctx, src)   (PLIC_BASE + 0x002000UL + 0x80UL * (ctx) + 4UL * ((src) / 32))

/* Priority threshold per context: offset 0x200000 + 0x1000*context */
#define PLIC_THRESHOLD(ctx)     (PLIC_BASE + 0x200000UL + 0x1000UL * (ctx))

/* Claim/complete per context: offset 0x200004 + 0x1000*context */
#define PLIC_CLAIM(ctx)         (PLIC_BASE + 0x200004UL + 0x1000UL * (ctx))

/* ── Maximum counts ───────────────────────────────────────────────── */

#define PLIC_MAX_SOURCES        128
#define PLIC_MAX_PRIORITY       7

/* ── Hart context IDs for QEMU virt ───────────────────────────────── */
/*
 * QEMU virt with one hart:
 *   Context 0 = Hart 0, M-mode
 *   Context 1 = Hart 0, S-mode
 */
#define PLIC_CONTEXT_M0         0
#define PLIC_CONTEXT_S0         1

/* ── MMIO helpers ─────────────────────────────────────────────────── */

static inline void plic_write32(uint64_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static inline uint32_t plic_read32(uint64_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Public API ───────────────────────────────────────────────────── */

void     plic_init(void);
void     plic_set_priority(uint32_t source, uint32_t priority);
void     plic_set_threshold(uint32_t context, uint32_t threshold);
void     plic_enable(uint32_t context, uint32_t source);
void     plic_disable(uint32_t context, uint32_t source);
uint32_t plic_claim(uint32_t context);
void     plic_complete(uint32_t context, uint32_t source);
bool     plic_is_pending(uint32_t source);

#endif /* ARCH_RISCV64_BOOT_PLIC_H */
