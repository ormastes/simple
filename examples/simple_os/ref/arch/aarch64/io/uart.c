/*
 * uart.c — PL011 UART driver for AArch64 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/aarch64/io/uart.h"

/* ── Initialisation ────────────────────────────────────────────────── */

void uart_init(void)
{
    uint64_t base = PL011_BASE;

    /* Disable UART while configuring */
    mmio_write32(base + UART_CR, 0);

    /* Clear all pending interrupts */
    mmio_write32(base + UART_ICR, 0x7FF);

    /*
     * Baud rate calculation for 115200 with 24 MHz clock:
     *   BRD = UARTCLK / (16 * Baud) = 24000000 / (16 * 115200) = 13.0208...
     *   IBRD = 13
     *   FBRD = round(0.0208 * 64) = 1
     */
    mmio_write32(base + UART_IBRD, 13);
    mmio_write32(base + UART_FBRD, 1);

    /* 8 bits, FIFO enabled, no parity, 1 stop bit */
    mmio_write32(base + UART_LCR_H, LCR_WLEN_8 | LCR_FEN);

    /* Mask all interrupts (polling mode) */
    mmio_write32(base + UART_IMSC, 0);

    /* Enable UART, TX, and RX */
    mmio_write32(base + UART_CR, CR_UARTEN | CR_TXE | CR_RXE);
}

/* ── Single-character I/O ──────────────────────────────────────────── */

void uart_putc(char c)
{
    uint64_t base = PL011_BASE;

    /* Wait until transmit FIFO is not full */
    while (mmio_read32(base + UART_FR) & FR_TXFF)
        ;
    mmio_write32(base + UART_DR, (uint32_t)c);
}

char uart_getc(void)
{
    /* Wait until data is available */
    while (!uart_has_data())
        ;
    return (char)(mmio_read32(PL011_BASE + UART_DR) & 0xFF);
}

bool uart_has_data(void)
{
    return (mmio_read32(PL011_BASE + UART_FR) & FR_RXFE) == 0;
}

/* ── String output helpers ─────────────────────────────────────────── */

void uart_write(const char *s)
{
    while (*s) {
        if (*s == '\n')
            uart_putc('\r');
        uart_putc(*s++);
    }
}

void uart_write_hex(uint64_t val)
{
    static const char hex[] = "0123456789abcdef";
    uart_putc('0');
    uart_putc('x');
    for (int i = 60; i >= 0; i -= 4) {
        uart_putc(hex[(val >> i) & 0xF]);
    }
}

void uart_write_dec(uint32_t val)
{
    if (val == 0) {
        uart_putc('0');
        return;
    }

    char buf[10];
    int  pos = 0;

    while (val > 0) {
        buf[pos++] = '0' + (char)(val % 10);
        val /= 10;
    }

    /* Print in reverse */
    while (pos > 0) {
        uart_putc(buf[--pos]);
    }
}
