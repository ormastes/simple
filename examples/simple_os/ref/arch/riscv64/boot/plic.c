/*
 * plic.c — Platform-Level Interrupt Controller for RISC-V 64-bit
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv64/boot/plic.h"

/* ── Initialisation ───────────────────────────────────────────────── */

void plic_init(void)
{
    /* Set all source priorities to 0 (disabled) */
    for (uint32_t i = 1; i < PLIC_MAX_SOURCES; i++) {
        plic_set_priority(i, 0);
    }

    /* Set threshold to 0 for M-mode context (accept all priorities > 0) */
    plic_set_threshold(PLIC_CONTEXT_M0, 0);
}

/* ── Priority ─────────────────────────────────────────────────────── */

void plic_set_priority(uint32_t source, uint32_t priority)
{
    if (source == 0 || source >= PLIC_MAX_SOURCES)
        return;
    if (priority > PLIC_MAX_PRIORITY)
        priority = PLIC_MAX_PRIORITY;
    plic_write32(PLIC_PRIORITY(source), priority);
}

/* ── Threshold ────────────────────────────────────────────────────── */

void plic_set_threshold(uint32_t context, uint32_t threshold)
{
    plic_write32(PLIC_THRESHOLD(context), threshold);
}

/* ── Enable / Disable ─────────────────────────────────────────────── */

void plic_enable(uint32_t context, uint32_t source)
{
    if (source == 0 || source >= PLIC_MAX_SOURCES)
        return;
    uint64_t addr = PLIC_ENABLE(context, source);
    uint32_t bit  = 1U << (source % 32);
    uint32_t val  = plic_read32(addr);
    plic_write32(addr, val | bit);
}

void plic_disable(uint32_t context, uint32_t source)
{
    if (source == 0 || source >= PLIC_MAX_SOURCES)
        return;
    uint64_t addr = PLIC_ENABLE(context, source);
    uint32_t bit  = 1U << (source % 32);
    uint32_t val  = plic_read32(addr);
    plic_write32(addr, val & ~bit);
}

/* ── Claim / Complete ─────────────────────────────────────────────── */

uint32_t plic_claim(uint32_t context)
{
    return plic_read32(PLIC_CLAIM(context));
}

void plic_complete(uint32_t context, uint32_t source)
{
    plic_write32(PLIC_CLAIM(context), source);
}

/* ── Pending query ────────────────────────────────────────────────── */

bool plic_is_pending(uint32_t source)
{
    if (source == 0 || source >= PLIC_MAX_SOURCES)
        return false;
    uint32_t val = plic_read32(PLIC_PENDING(source));
    return (val & (1U << (source % 32))) != 0;
}
