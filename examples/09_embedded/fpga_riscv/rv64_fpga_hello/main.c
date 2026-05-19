/* main.c — RV64 bare-metal FPGA hello payload
 *
 * Prints the proof string over UART then loops emitting tick markers.
 * No stdlib. No heap. No SBI calls.
 *
 * UART: NS16550-compatible at UART_BASE (configurable via -DUART_BASE=0x...).
 * Default: 0x10000000 (Zynq PS UART0 or soft-core 16550 bridge).
 */

#ifndef UART_BASE
#define UART_BASE  0x10000000UL
#endif

/* NS16550 register offsets (byte-wide, 8-bit MMIO) */
#define UART_THR   0x00   /* Transmit Holding Register (write) */
#define UART_LSR   0x05   /* Line Status Register */
#define UART_LSR_THRE  (1 << 5)  /* TX Holding Register Empty */

/* ------------------------------------------------------------------ */
/* Low-level UART helpers                                               */
/* ------------------------------------------------------------------ */

static inline volatile unsigned char *uart_reg(unsigned long base, int offset)
{
    return (volatile unsigned char *)(base + (unsigned long)offset);
}

void uart_putchar(unsigned long base, char c)
{
    /* Spin until TX holding register is empty */
    while (!(*uart_reg(base, UART_LSR) & UART_LSR_THRE))
        ;
    *uart_reg(base, UART_THR) = (unsigned char)c;
}

void uart_puts(unsigned long base, const char *s)
{
    while (*s) {
        if (*s == '\n')
            uart_putchar(base, '\r');
        uart_putchar(base, *s++);
    }
}

/* Minimal hex printer — no sprintf, no stdlib */
static const char hex_digits[] = "0123456789abcdef";

void uart_put_hex64(unsigned long base, unsigned long val)
{
    uart_puts(base, "0x");
    for (int i = 60; i >= 0; i -= 4)
        uart_putchar(base, hex_digits[(val >> i) & 0xF]);
}

void uart_put_dec(unsigned long base, unsigned long val)
{
    char buf[20];
    int i = 0;
    if (val == 0) { uart_putchar(base, '0'); return; }
    while (val) { buf[i++] = '0' + (val % 10); val /= 10; }
    while (i--) uart_putchar(base, buf[i]);
}

/* ------------------------------------------------------------------ */
/* main                                                                 */
/* ------------------------------------------------------------------ */

int main(void)
{
    const unsigned long uart = UART_BASE;

    /* ---- Proof string ---- */
    uart_puts(uart, "SIMPLE-RV64-FPGA-HELLO board=zynq7020-ml-carrier hart=0 pc=");
    /* Read PC via auipc trick */
    unsigned long pc = 0;
    __asm__ volatile ("auipc %0, 0" : "=r"(pc));
    uart_put_hex64(uart, pc);
    uart_puts(uart, "\n");

    /* ---- Tick loop ---- */
    uart_puts(uart, "TICK ");
    unsigned long tick = 0;
    for (;;) {
        /* Busy-wait ~1M iterations as a rough delay */
        volatile unsigned long delay = 1000000UL;
        while (delay--)
            ;

        uart_put_dec(uart, tick++);
        uart_putchar(uart, ' ');

        /* Line-wrap every 16 ticks */
        if ((tick & 0xF) == 0)
            uart_puts(uart, "\nTICK ");
    }

    return 0; /* unreachable */
}
