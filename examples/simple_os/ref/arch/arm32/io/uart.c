/*
 * uart.c — PL011 UART driver for ARM32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/arm32/io/uart.h"

/* ── Initialisation ────────────────────────────────────────────────── */

void uart_init(void)
{
    /* Disable UART while configuring */
    mmio_write32(UART0_BASE + UART_CR, 0x00);

    /* Clear all pending interrupts */
    mmio_write32(UART0_BASE + UART_ICR, 0x7FF);

    /*
     * Set baud rate to 115200 with 24 MHz clock.
     *
     * BRD = UARTCLK / (16 * baud) = 24000000 / (16 * 115200) = 13.0208...
     * IBRD = 13
     * FBRD = round(0.0208 * 64) = round(1.333) = 1
     */
    mmio_write32(UART0_BASE + UART_IBRD, 13);
    mmio_write32(UART0_BASE + UART_FBRD, 1);

    /* 8 data bits, no parity, 1 stop bit, enable FIFOs */
    mmio_write32(UART0_BASE + UART_LCR_H, LCR_H_WLEN_8 | LCR_H_FEN);

    /* Mask all interrupts (we poll) */
    mmio_write32(UART0_BASE + UART_IMSC, 0x00);

    /* Enable UART, TX, and RX */
    mmio_write32(UART0_BASE + UART_CR, CR_UARTEN | CR_TXE | CR_RXE);
}

/* ── Single-character I/O ──────────────────────────────────────────── */

void uart_putc(char c)
{
    /* Wait while transmit FIFO is full */
    while (mmio_read32(UART0_BASE + UART_FR) & FR_TXFF)
        ;
    mmio_write32(UART0_BASE + UART_DR, (uint32_t)c);
}

char uart_getc(void)
{
    /* Wait while receive FIFO is empty */
    while (!uart_has_data())
        ;
    return (char)(mmio_read32(UART0_BASE + UART_DR) & 0xFF);
}

bool uart_has_data(void)
{
    return (mmio_read32(UART0_BASE + UART_FR) & FR_RXFE) == 0;
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

void uart_write_hex(uint32_t val)
{
    static const char hex[] = "0123456789abcdef";
    uart_putc('0');
    uart_putc('x');
    for (int i = 28; i >= 0; i -= 4) {
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
