/*
 * uart.h — PL011 UART driver for AArch64 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_AARCH64_IO_UART_H
#define ARCH_AARCH64_IO_UART_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── PL011 UART base address (QEMU -M virt) ──────────────────────── */

#define PL011_BASE      0x09000000UL

/* ── PL011 register offsets ───────────────────────────────────────── */

#define UART_DR         0x000   /* Data Register (R/W)                */
#define UART_FR         0x018   /* Flag Register (RO)                 */
#define UART_IBRD       0x024   /* Integer Baud Rate Divisor          */
#define UART_FBRD       0x028   /* Fractional Baud Rate Divisor       */
#define UART_LCR_H      0x02C   /* Line Control Register              */
#define UART_CR         0x030   /* Control Register                   */
#define UART_IMSC       0x038   /* Interrupt Mask Set/Clear           */
#define UART_ICR        0x044   /* Interrupt Clear Register           */

/* ── Flag Register bits ───────────────────────────────────────────── */

#define FR_RXFE         (1 << 4)    /* Receive FIFO empty             */
#define FR_TXFF         (1 << 5)    /* Transmit FIFO full             */
#define FR_BUSY         (1 << 3)    /* UART busy                      */

/* ── Control Register bits ────────────────────────────────────────── */

#define CR_UARTEN       (1 << 0)    /* UART enable                    */
#define CR_TXE          (1 << 8)    /* Transmit enable                */
#define CR_RXE          (1 << 9)    /* Receive enable                 */

/* ── Line Control Register bits ───────────────────────────────────── */

#define LCR_FEN         (1 << 4)    /* FIFO enable                    */
#define LCR_WLEN_8      (3 << 5)    /* Word length 8 bits             */

/* ── Clock and baud rate ──────────────────────────────────────────── */

#define UART_CLOCK_HZ   24000000    /* 24 MHz reference clock         */
#define UART_BAUD_RATE  115200

/* ── MMIO helpers ─────────────────────────────────────────────────── */

static inline void mmio_write32(uint64_t addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static inline uint32_t mmio_read32(uint64_t addr)
{
    return *(volatile uint32_t *)addr;
}

/* ── Public API ────────────────────────────────────────────────────── */

void uart_init(void);
void uart_putc(char c);
char uart_getc(void);
bool uart_has_data(void);
void uart_write(const char *s);
void uart_write_hex(uint64_t val);
void uart_write_dec(uint32_t val);

#endif /* ARCH_AARCH64_IO_UART_H */
