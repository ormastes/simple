/*
 * plic.c — PLIC (Platform-Level Interrupt Controller) for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/boot/plic.h"

/* ── MMIO helpers ────────────────────────────────────────────────────── */

static inline void plic_write(uint32_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static inline uint32_t plic_read(uint32_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Initialisation ──────────────────────────────────────────────────── */

void plic_init(void)
{
    /* Set all interrupt priorities to 0 (disabled) */
    for (uint32_t i = 1; i < PLIC_MAX_IRQS; i++) {
        plic_write(PLIC_PRIORITY_BASE + i * 4, 0);
    }

    /* Disable all interrupts for M-mode context 0 */
    for (uint32_t i = 0; i < (PLIC_MAX_IRQS + 31) / 32; i++) {
        plic_write(PLIC_ENABLE_BASE + PLIC_CONTEXT_M0 * PLIC_ENABLE_STRIDE + i * 4, 0);
    }

    /* Set threshold to 0 (accept all priorities > 0) */
    plic_set_threshold(PLIC_CONTEXT_M0, 0);
}

/* ── IRQ enable / disable ────────────────────────────────────────────── */

void plic_enable_irq(uint32_t irq)
{
    if (irq == 0 || irq >= PLIC_MAX_IRQS)
        return;

    uint32_t word = irq / 32;
    uint32_t bit  = irq % 32;
    uint32_t addr = PLIC_ENABLE_BASE + PLIC_CONTEXT_M0 * PLIC_ENABLE_STRIDE + word * 4;

    uint32_t val = plic_read(addr);
    val |= (1U << bit);
    plic_write(addr, val);
}

void plic_disable_irq(uint32_t irq)
{
    if (irq == 0 || irq >= PLIC_MAX_IRQS)
        return;

    uint32_t word = irq / 32;
    uint32_t bit  = irq % 32;
    uint32_t addr = PLIC_ENABLE_BASE + PLIC_CONTEXT_M0 * PLIC_ENABLE_STRIDE + word * 4;

    uint32_t val = plic_read(addr);
    val &= ~(1U << bit);
    plic_write(addr, val);
}

/* ── Priority and threshold ──────────────────────────────────────────── */

void plic_set_priority(uint32_t irq, uint32_t priority)
{
    if (irq == 0 || irq >= PLIC_MAX_IRQS)
        return;

    plic_write(PLIC_PRIORITY_BASE + irq * 4, priority);
}

void plic_set_threshold(uint32_t context, uint32_t threshold)
{
    uint32_t addr = PLIC_THRESHOLD_BASE + context * PLIC_CONTEXT_STRIDE;
    plic_write(addr, threshold);
}

/* ── Claim / complete ────────────────────────────────────────────────── */

uint32_t plic_claim(uint32_t context)
{
    uint32_t addr = PLIC_CLAIM_BASE + context * PLIC_CONTEXT_STRIDE;
    return plic_read(addr);
}

void plic_complete(uint32_t context, uint32_t irq)
{
    uint32_t addr = PLIC_CLAIM_BASE + context * PLIC_CONTEXT_STRIDE;
    plic_write(addr, irq);
}
