/*
 * uart.h — PL011 UART driver for ARM32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_ARM32_IO_UART_H
#define ARCH_ARM32_IO_UART_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PL011 UART base address (QEMU -M virt) ──────────────────────── */

#define UART0_BASE      0x09000000

/* ── PL011 register offsets ───────────────────────────────────────── */

#define UART_DR         0x000   /* Data Register                     */
#define UART_RSR        0x004   /* Receive Status / Error Clear      */
#define UART_FR         0x018   /* Flag Register                     */
#define UART_ILPR       0x020   /* IrDA Low-Power Counter            */
#define UART_IBRD       0x024   /* Integer Baud Rate Divisor         */
#define UART_FBRD       0x028   /* Fractional Baud Rate Divisor      */
#define UART_LCR_H      0x02C   /* Line Control Register             */
#define UART_CR         0x030   /* Control Register                  */
#define UART_IFLS       0x034   /* Interrupt FIFO Level Select       */
#define UART_IMSC       0x038   /* Interrupt Mask Set/Clear          */
#define UART_RIS        0x03C   /* Raw Interrupt Status              */
#define UART_MIS        0x040   /* Masked Interrupt Status           */
#define UART_ICR        0x044   /* Interrupt Clear Register          */
#define UART_DMACR      0x048   /* DMA Control Register              */

/* ── Flag Register bits ───────────────────────────────────────────── */

#define FR_RXFE         (1 << 4)    /* Receive FIFO empty            */
#define FR_TXFF         (1 << 5)    /* Transmit FIFO full            */
#define FR_RXFF         (1 << 6)    /* Receive FIFO full             */
#define FR_TXFE         (1 << 7)    /* Transmit FIFO empty           */
#define FR_BUSY         (1 << 3)    /* UART busy                     */

/* ── Control Register bits ────────────────────────────────────────── */

#define CR_UARTEN       (1 << 0)    /* UART enable                   */
#define CR_TXE          (1 << 8)    /* Transmit enable               */
#define CR_RXE          (1 << 9)    /* Receive enable                */

/* ── Line Control Register bits ───────────────────────────────────── */

#define LCR_H_WLEN_8    (3 << 5)    /* 8 data bits                   */
#define LCR_H_FEN       (1 << 4)    /* Enable FIFOs                  */
#define LCR_H_STP2      (1 << 3)    /* Two stop bits                 */

/* ── Baud rate constants (assuming 24 MHz UARTCLK) ────────────────── */

#define UART_CLOCK_HZ   24000000
#define UART_BAUD_RATE  115200

/* ── MMIO helpers ─────────────────────────────────────────────────── */

INLINE void mmio_write32(uint32_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

INLINE uint32_t mmio_read32(uint32_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Public API ────────────────────────────────────────────────────── */

void uart_init(void);
void uart_putc(char c);
char uart_getc(void);
bool uart_has_data(void);
void uart_write(const char *s);
void uart_write_hex(uint32_t val);
void uart_write_dec(uint32_t val);

#endif /* ARCH_ARM32_IO_UART_H */
