/*
 * gic.h — GICv2 interrupt controller for ARM32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_ARM32_BOOT_GIC_H
#define ARCH_ARM32_BOOT_GIC_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── GICv2 base addresses (QEMU -M virt) ──────────────────────────── */

#define GICD_BASE           0x08000000  /* Distributor               */
#define GICC_BASE           0x08010000  /* CPU Interface             */

/* ── Distributor registers ────────────────────────────────────────── */

#define GICD_CTLR           (GICD_BASE + 0x000)  /* Control          */
#define GICD_TYPER          (GICD_BASE + 0x004)  /* Type             */
#define GICD_ISENABLER(n)   (GICD_BASE + 0x100 + 4 * (n))  /* Set-Enable    */
#define GICD_ICENABLER(n)   (GICD_BASE + 0x180 + 4 * (n))  /* Clear-Enable  */
#define GICD_ISPENDR(n)     (GICD_BASE + 0x200 + 4 * (n))  /* Set-Pending   */
#define GICD_ICPENDR(n)     (GICD_BASE + 0x280 + 4 * (n))  /* Clear-Pending */
#define GICD_IPRIORITYR(n)  (GICD_BASE + 0x400 + 4 * (n))  /* Priority      */
#define GICD_ITARGETSR(n)   (GICD_BASE + 0x800 + 4 * (n))  /* Target CPU    */
#define GICD_ICFGR(n)       (GICD_BASE + 0xC00 + 4 * (n))  /* Configuration */

/* ── CPU Interface registers ──────────────────────────────────────── */

#define GICC_CTLR           (GICC_BASE + 0x000)  /* Control          */
#define GICC_PMR            (GICC_BASE + 0x004)  /* Priority Mask    */
#define GICC_BPR            (GICC_BASE + 0x008)  /* Binary Point     */
#define GICC_IAR            (GICC_BASE + 0x00C)  /* Interrupt Ack    */
#define GICC_EOIR           (GICC_BASE + 0x010)  /* End of Interrupt */

/* ── Constants ─────────────────────────────────────────────────────── */

#define GIC_MAX_IRQS        256
#define GIC_SPURIOUS_IRQ    1023

/* ── MMIO helpers ─────────────────────────────────────────────────── */

INLINE void gic_write32(uint32_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

INLINE uint32_t gic_read32(uint32_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Public API ────────────────────────────────────────────────────── */

void     gic_init(void);
void     gic_enable_irq(uint32_t irq);
void     gic_disable_irq(uint32_t irq);
uint32_t gic_acknowledge(void);
void     gic_end_interrupt(uint32_t irq);
void     gic_set_priority(uint32_t irq, uint8_t prio);
void     gic_set_target(uint32_t irq, uint8_t cpu_mask);
bool     gic_is_pending(uint32_t irq);

#endif /* ARCH_ARM32_BOOT_GIC_H */
