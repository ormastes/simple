/*
 * uart.c — 16550 UART driver for RISC-V32 (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#include "arch/riscv32/io/uart.h"

/* ── Initialisation ──────────────────────────────────────────────────── */

void uart_init(void)
{
    /* Disable all interrupts */
    uart_mmio_write(UART_IER, 0x00);

    /* Enable DLAB (set baud rate divisor) */
    uart_mmio_write(UART_LCR, LCR_DLAB);

    /* Set divisor (lo byte / hi byte) — 115200 baud */
    uart_mmio_write(UART_DLL, (uint8_t)(UART_DIVISOR & 0xFF));
    uart_mmio_write(UART_DLH, (uint8_t)((UART_DIVISOR >> 8) & 0xFF));

    /* 8 bits, no parity, one stop bit (8N1), clear DLAB */
    uart_mmio_write(UART_LCR, LCR_8N1);

    /* Enable FIFO, clear them, 14-byte threshold */
    uart_mmio_write(UART_FCR, 0xC7);

    /* DTR + RTS + OUT2 (required for interrupts) */
    uart_mmio_write(UART_MCR, 0x0B);
}

/* ── Single-character I/O ────────────────────────────────────────────── */

void uart_putc(char c)
{
    /* Wait until Transmitter Holding Register is empty */
    while ((uart_mmio_read(UART_LSR) & LSR_THRE) == 0)
        ;
    uart_mmio_write(UART_THR, (uint8_t)c);
}

char uart_getc(void)
{
    /* Wait until data is ready */
    while (!uart_has_data())
        ;
    return (char)uart_mmio_read(UART_RBR);
}

bool uart_has_data(void)
{
    return (uart_mmio_read(UART_LSR) & LSR_DATA_READY) != 0;
}

/* ── String output helpers ───────────────────────────────────────────── */

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
