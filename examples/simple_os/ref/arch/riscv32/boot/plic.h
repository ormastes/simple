/*
 * plic.h — PLIC (Platform-Level Interrupt Controller) for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * QEMU virt PLIC base: 0x0C000000
 *
 * PLIC memory map:
 *   0x0C000000 + irq*4         : Priority registers (1 per source)
 *   0x0C001000                 : Pending bits
 *   0x0C002000 + ctx*0x80      : Enable bits (per context)
 *   0x0C200000 + ctx*0x1000    : Threshold + claim/complete (per context)
 */

#ifndef ARCH_RISCV32_BOOT_PLIC_H
#define ARCH_RISCV32_BOOT_PLIC_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PLIC base address (QEMU virt) ───────────────────────────────────── */

#define PLIC_BASE           0x0C000000

/* ── PLIC register offsets ───────────────────────────────────────────── */

#define PLIC_PRIORITY_BASE  (PLIC_BASE + 0x000000)
#define PLIC_PENDING_BASE   (PLIC_BASE + 0x001000)
#define PLIC_ENABLE_BASE    (PLIC_BASE + 0x002000)
#define PLIC_THRESHOLD_BASE (PLIC_BASE + 0x200000)
#define PLIC_CLAIM_BASE     (PLIC_BASE + 0x200004)

/* Context stride (each hart context has 0x1000 bytes for threshold/claim) */
#define PLIC_CONTEXT_STRIDE     0x1000
/* Enable stride (each hart context has 0x80 bytes for enable bits) */
#define PLIC_ENABLE_STRIDE      0x80

/* Maximum number of interrupt sources */
#define PLIC_MAX_IRQS       128

/* QEMU virt M-mode context for hart 0 */
#define PLIC_CONTEXT_M0     0
/* QEMU virt S-mode context for hart 0 */
#define PLIC_CONTEXT_S0     1

/* UART0 IRQ on QEMU virt */
#define PLIC_UART0_IRQ      10

/* ── Public API ──────────────────────────────────────────────────────── */

void     plic_init(void);
void     plic_enable_irq(uint32_t irq);
void     plic_disable_irq(uint32_t irq);
void     plic_set_priority(uint32_t irq, uint32_t priority);
void     plic_set_threshold(uint32_t context, uint32_t threshold);
uint32_t plic_claim(uint32_t context);
void     plic_complete(uint32_t context, uint32_t irq);

#endif /* ARCH_RISCV32_BOOT_PLIC_H */
