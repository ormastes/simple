/*
 * gic.c — GICv2 (Generic Interrupt Controller) for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/boot/gic.h"
#include "arch/aarch64/io/uart.h"  /* mmio_read32 / mmio_write32 */

/* ── Helpers ───────────────────────────────────────────────────────── */

static inline void gicd_write(uint32_t offset, uint32_t val)
{
    mmio_write32(GICD_BASE + offset, val);
}

static inline uint32_t gicd_read(uint32_t offset)
{
    return mmio_read32(GICD_BASE + offset);
}

static inline void gicc_write(uint32_t offset, uint32_t val)
{
    mmio_write32(GICC_BASE + offset, val);
}

static inline uint32_t gicc_read(uint32_t offset)
{
    return mmio_read32(GICC_BASE + offset);
}

/* ── Initialisation ────────────────────────────────────────────────── */

void gic_init(void)
{
    /* Disable distributor while configuring */
    gicd_write(GICD_CTLR, 0);

    /*
     * Read the number of supported interrupt lines.
     * ITLinesNumber = (TYPER & 0x1F), max SPI = 32 * (N + 1)
     */
    uint32_t typer = gicd_read(GICD_TYPER);
    uint32_t num_lines = 32 * ((typer & 0x1F) + 1);
    if (num_lines > GIC_MAX_IRQ)
        num_lines = GIC_MAX_IRQ;

    /* Disable all interrupts */
    for (uint32_t i = 0; i < num_lines / 32; i++) {
        gicd_write(GICD_ICENABLER + i * 4, 0xFFFFFFFF);
    }

    /* Set all interrupts to lowest priority (0xFF) */
    for (uint32_t i = 0; i < num_lines / 4; i++) {
        gicd_write(GICD_IPRIORITYR + i * 4, 0xFFFFFFFF);
    }

    /* Target all SPIs to CPU 0 */
    for (uint32_t i = 8; i < num_lines / 4; i++) {
        gicd_write(GICD_ITARGETSR + i * 4, 0x01010101);
    }

    /* Configure all SPIs as level-triggered */
    for (uint32_t i = 2; i < num_lines / 16; i++) {
        gicd_write(GICD_ICFGR + i * 4, 0x00000000);
    }

    /* Enable the distributor */
    gicd_write(GICD_CTLR, GICD_CTLR_ENABLE);

    /* Enable the CPU interface */
    gicc_write(GICC_CTLR, GICC_CTLR_ENABLE);

    /* Set priority mask to accept all priorities */
    gicc_write(GICC_PMR, 0xFF);
}

/* ── Enable / disable individual IRQs ──────────────────────────────── */

void gic_enable_irq(uint32_t irq)
{
    if (irq >= GIC_MAX_IRQ)
        return;
    uint32_t reg = irq / 32;
    uint32_t bit = irq % 32;
    gicd_write(GICD_ISENABLER + reg * 4, 1 << bit);
}

void gic_disable_irq(uint32_t irq)
{
    if (irq >= GIC_MAX_IRQ)
        return;
    uint32_t reg = irq / 32;
    uint32_t bit = irq % 32;
    gicd_write(GICD_ICENABLER + reg * 4, 1 << bit);
}

/* ── Interrupt acknowledge / end ───────────────────────────────────── */

uint32_t gic_acknowledge(void)
{
    return gicc_read(GICC_IAR) & 0x3FF;    /* IRQ ID in bits [9:0] */
}

void gic_end_interrupt(uint32_t irq)
{
    gicc_write(GICC_EOIR, irq);
}

/* ── Priority and target configuration ─────────────────────────────── */

void gic_set_priority(uint32_t irq, uint8_t priority)
{
    if (irq >= GIC_MAX_IRQ)
        return;
    uint32_t reg = irq / 4;
    uint32_t shift = (irq % 4) * 8;
    uint32_t val = gicd_read(GICD_IPRIORITYR + reg * 4);
    val &= ~(0xFF << shift);
    val |= ((uint32_t)priority) << shift;
    gicd_write(GICD_IPRIORITYR + reg * 4, val);
}

void gic_set_target(uint32_t irq, uint8_t cpu_mask)
{
    if (irq >= GIC_MAX_IRQ)
        return;
    uint32_t reg = irq / 4;
    uint32_t shift = (irq % 4) * 8;
    uint32_t val = gicd_read(GICD_ITARGETSR + reg * 4);
    val &= ~(0xFF << shift);
    val |= ((uint32_t)cpu_mask) << shift;
    gicd_write(GICD_ITARGETSR + reg * 4, val);
}
