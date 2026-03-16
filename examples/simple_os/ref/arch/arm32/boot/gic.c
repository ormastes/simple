/*
 * gic.c — GICv2 interrupt controller for ARM32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/boot/gic.h"

/* ── Initialisation ────────────────────────────────────────────────── */

void gic_init(void)
{
    /* Disable distributor while configuring */
    gic_write32(GICD_CTLR, 0x00);

    /* Read TYPER to determine number of interrupt lines */
    uint32_t typer = gic_read32(GICD_TYPER);
    uint32_t num_lines = ((typer & 0x1F) + 1) * 32;
    if (num_lines > GIC_MAX_IRQS)
        num_lines = GIC_MAX_IRQS;

    /* Disable all interrupts */
    for (uint32_t i = 0; i < num_lines / 32; i++) {
        gic_write32(GICD_ICENABLER(i), 0xFFFFFFFF);
    }

    /* Clear all pending interrupts */
    for (uint32_t i = 0; i < num_lines / 32; i++) {
        gic_write32(GICD_ICPENDR(i), 0xFFFFFFFF);
    }

    /* Set all interrupts to lowest priority (0xFF) */
    for (uint32_t i = 0; i < num_lines / 4; i++) {
        gic_write32(GICD_IPRIORITYR(i), 0xFFFFFFFF);
    }

    /* Target all SPIs to CPU0 */
    for (uint32_t i = 8; i < num_lines / 4; i++) {
        gic_write32(GICD_ITARGETSR(i), 0x01010101);
    }

    /* Configure all SPIs as level-triggered */
    for (uint32_t i = 2; i < num_lines / 16; i++) {
        gic_write32(GICD_ICFGR(i), 0x00000000);
    }

    /* Enable distributor */
    gic_write32(GICD_CTLR, 0x01);

    /* ── CPU Interface setup ── */

    /* Set priority mask to accept all priorities */
    gic_write32(GICC_PMR, 0xFF);

    /* No priority grouping (all bits for priority, none for sub-priority) */
    gic_write32(GICC_BPR, 0x00);

    /* Enable CPU interface */
    gic_write32(GICC_CTLR, 0x01);
}

/* ── IRQ enable / disable ──────────────────────────────────────────── */

void gic_enable_irq(uint32_t irq)
{
    if (irq >= GIC_MAX_IRQS)
        return;
    uint32_t reg = irq / 32;
    uint32_t bit = irq % 32;
    gic_write32(GICD_ISENABLER(reg), (uint32_t)(1 << bit));
}

void gic_disable_irq(uint32_t irq)
{
    if (irq >= GIC_MAX_IRQS)
        return;
    uint32_t reg = irq / 32;
    uint32_t bit = irq % 32;
    gic_write32(GICD_ICENABLER(reg), (uint32_t)(1 << bit));
}

/* ── Acknowledge / End of Interrupt ───────────────────────────────── */

uint32_t gic_acknowledge(void)
{
    return gic_read32(GICC_IAR) & 0x3FF;
}

void gic_end_interrupt(uint32_t irq)
{
    gic_write32(GICC_EOIR, irq);
}

/* ── Priority and target configuration ────────────────────────────── */

void gic_set_priority(uint32_t irq, uint8_t prio)
{
    if (irq >= GIC_MAX_IRQS)
        return;

    uint32_t reg_offset = irq / 4;
    uint32_t byte_offset = irq % 4;
    uint32_t addr = GICD_BASE + 0x400 + reg_offset * 4;

    uint32_t val = gic_read32(addr);
    val &= ~(0xFFU << (byte_offset * 8));
    val |= ((uint32_t)prio << (byte_offset * 8));
    gic_write32(addr, val);
}

void gic_set_target(uint32_t irq, uint8_t cpu_mask)
{
    if (irq < 32 || irq >= GIC_MAX_IRQS)
        return;  /* SGI/PPI targets are read-only */

    uint32_t reg_offset = irq / 4;
    uint32_t byte_offset = irq % 4;
    uint32_t addr = GICD_BASE + 0x800 + reg_offset * 4;

    uint32_t val = gic_read32(addr);
    val &= ~(0xFFU << (byte_offset * 8));
    val |= ((uint32_t)cpu_mask << (byte_offset * 8));
    gic_write32(addr, val);
}

/* ── Status queries ───────────────────────────────────────────────── */

bool gic_is_pending(uint32_t irq)
{
    if (irq >= GIC_MAX_IRQS)
        return false;
    uint32_t reg = irq / 32;
    uint32_t bit = irq % 32;
    return (gic_read32(GICD_ISPENDR(reg)) & (1 << bit)) != 0;
}
