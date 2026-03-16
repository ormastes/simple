/*
 * gic.h — GICv2 (Generic Interrupt Controller) for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * QEMU -M virt uses GICv2 with:
 *   GICD (Distributor)  at 0x08000000
 *   GICC (CPU Interface) at 0x08010000
 */

#ifndef ARCH_AARCH64_BOOT_GIC_H
#define ARCH_AARCH64_BOOT_GIC_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── GICv2 base addresses (QEMU -M virt) ──────────────────────────── */

#define GICD_BASE       0x08000000UL
#define GICC_BASE       0x08010000UL

/* ── GICD (Distributor) register offsets ───────────────────────────── */

#define GICD_CTLR       0x000   /* Distributor Control Register       */
#define GICD_TYPER      0x004   /* Interrupt Controller Type Register  */
#define GICD_ISENABLER  0x100   /* Interrupt Set-Enable Registers      */
#define GICD_ICENABLER  0x180   /* Interrupt Clear-Enable Registers    */
#define GICD_ISPENDR    0x200   /* Interrupt Set-Pending Registers     */
#define GICD_ICPENDR    0x280   /* Interrupt Clear-Pending Registers   */
#define GICD_IPRIORITYR 0x400   /* Interrupt Priority Registers        */
#define GICD_ITARGETSR  0x800   /* Interrupt Processor Targets Regs    */
#define GICD_ICFGR      0xC00   /* Interrupt Configuration Registers   */

/* ── GICC (CPU Interface) register offsets ─────────────────────────── */

#define GICC_CTLR       0x000   /* CPU Interface Control Register      */
#define GICC_PMR        0x004   /* Interrupt Priority Mask Register     */
#define GICC_IAR        0x00C   /* Interrupt Acknowledge Register       */
#define GICC_EOIR       0x010   /* End of Interrupt Register            */

/* ── GICD_CTLR bits ───────────────────────────────────────────────── */

#define GICD_CTLR_ENABLE    1

/* ── GICC_CTLR bits ───────────────────────────────────────────────── */

#define GICC_CTLR_ENABLE    1

/* ── Special interrupt IDs ─────────────────────────────────────────── */

#define GIC_SPURIOUS_IRQ    1023
#define GIC_MAX_IRQ         256

/* ── Timer IRQ numbers (GIC SPI/PPI) ───────────────────────────────── */

#define GIC_PPI_PHYS_TIMER  30      /* Physical timer PPI (ID 30)      */
#define GIC_PPI_VIRT_TIMER  27      /* Virtual timer PPI (ID 27)       */

/* ── Public API ────────────────────────────────────────────────────── */

void     gic_init(void);
void     gic_enable_irq(uint32_t irq);
void     gic_disable_irq(uint32_t irq);
uint32_t gic_acknowledge(void);
void     gic_end_interrupt(uint32_t irq);
void     gic_set_priority(uint32_t irq, uint8_t priority);
void     gic_set_target(uint32_t irq, uint8_t cpu_mask);

#endif /* ARCH_AARCH64_BOOT_GIC_H */
