/*
 * pic.h — 8259 Programmable Interrupt Controller for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_X86_BOOT_PIC_H
#define ARCH_X86_BOOT_PIC_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"
#include "arch/x86/io/uart.h"  /* outb / inb */

/* ── PIC port addresses ────────────────────────────────────────────── */

#define PIC1_COMMAND    0x20
#define PIC1_DATA       0x21
#define PIC2_COMMAND    0xA0
#define PIC2_DATA       0xA1

/* ── ICW / OCW constants ───────────────────────────────────────────── */

#define ICW1_ICW4       0x01    /* ICW4 needed                       */
#define ICW1_INIT       0x10    /* Initialisation command             */
#define ICW4_8086       0x01    /* 8086/88 mode                      */

#define PIC_EOI         0x20    /* End of Interrupt                   */
#define PIC_READ_ISR    0x0B    /* Read In-Service Register           */
#define PIC_READ_IRR    0x0A    /* Read Interrupt Request Register    */

/* IRQ remap offsets */
#define PIC1_OFFSET     32      /* IRQ 0..7  -> vectors 32..39       */
#define PIC2_OFFSET     40      /* IRQ 8..15 -> vectors 40..47       */

/* ── Public API ────────────────────────────────────────────────────── */

void     pic_init(void);
void     pic_send_eoi(uint8_t irq);
void     pic_mask_irq(uint8_t irq);
void     pic_unmask_irq(uint8_t irq);
uint16_t pic_get_isr(void);
uint16_t pic_get_irr(void);
bool     pic_is_spurious(uint8_t irq);

#endif /* ARCH_X86_BOOT_PIC_H */
