/*
 * uart.h — 16550 UART driver for RISC-V32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 * MMIO-mapped 16550 UART at 0x10000000.
 */

#ifndef ARCH_RISCV32_IO_UART_H
#define ARCH_RISCV32_IO_UART_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── UART MMIO base address (QEMU virt) ──────────────────────────────── */

#define UART0_BASE      0x10000000

/* ── 16550 register offsets ──────────────────────────────────────────── */

#define UART_THR        0x00    /* Transmitter Holding Register (W)     */
#define UART_RBR        0x00    /* Receiver Buffer Register (R)         */
#define UART_DLL        0x00    /* Divisor Latch Low (DLAB=1)           */
#define UART_IER        0x01    /* Interrupt Enable Register            */
#define UART_DLH        0x01    /* Divisor Latch High (DLAB=1)          */
#define UART_FCR        0x02    /* FIFO Control Register (W)            */
#define UART_IIR        0x02    /* Interrupt Identification Reg (R)     */
#define UART_LCR        0x03    /* Line Control Register                */
#define UART_MCR        0x04    /* Modem Control Register               */
#define UART_LSR        0x05    /* Line Status Register                 */
#define UART_MSR        0x06    /* Modem Status Register                */
#define UART_SCR        0x07    /* Scratch Register                     */

/* Baud rate configuration */
#define UART_CLOCK_HZ   1843200
#define UART_BAUD       115200
#define UART_DIVISOR    (UART_CLOCK_HZ / (16 * UART_BAUD))  /* == 1 */

/* Line Status Register bits */
#define LSR_DATA_READY  0x01
#define LSR_THRE        0x20    /* Transmitter Holding Register Empty   */

/* LCR bits */
#define LCR_8N1         0x03    /* 8 data bits, no parity, 1 stop bit   */
#define LCR_DLAB        0x80    /* Divisor Latch Access Bit             */

/* ── MMIO helpers ────────────────────────────────────────────────────── */

static inline void uart_mmio_write(uint32_t offset, uint8_t val)
{
    *(volatile uint8_t *)(UART0_BASE + offset) = val;
}

static inline uint8_t uart_mmio_read(uint32_t offset)
{
    return *(volatile uint8_t *)(UART0_BASE + offset);
}

/* ── Public API ──────────────────────────────────────────────────────── */

void uart_init(void);
void uart_putc(char c);
char uart_getc(void);
bool uart_has_data(void);
void uart_write(const char *s);
void uart_write_hex(uint32_t val);
void uart_write_dec(uint32_t val);

#endif /* ARCH_RISCV32_IO_UART_H */
